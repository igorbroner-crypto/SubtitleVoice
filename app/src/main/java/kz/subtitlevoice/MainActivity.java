package kz.subtitlevoice;

import android.Manifest;
import android.app.AlertDialog;
import android.widget.CheckBox;
import android.widget.ProgressBar;
import java.net.URLEncoder;
import java.io.ByteArrayOutputStream;
import android.content.pm.PackageManager;
import android.content.pm.ActivityInfo;
import android.content.res.Configuration;
import android.view.Surface;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.Rect;
import android.graphics.RectF;
import android.graphics.Matrix;
import android.util.Size;
import java.nio.ByteBuffer;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.content.Intent;
import android.os.Build;
import android.speech.tts.TextToSpeech;
import android.speech.tts.Voice;
import android.view.Gravity;
import android.view.View;
import android.widget.*;
import android.content.SharedPreferences;

import androidx.activity.result.ActivityResultLauncher;
import androidx.activity.result.contract.ActivityResultContracts;
import androidx.annotation.NonNull;
import androidx.appcompat.app.AppCompatActivity;
import androidx.camera.core.CameraSelector;
import androidx.camera.core.Camera;
import androidx.camera.core.UseCaseGroup;
import androidx.camera.core.ViewPort;
import androidx.camera.core.ZoomState;
import androidx.camera.core.ImageAnalysis;
import androidx.camera.core.ImageProxy;
import androidx.camera.core.Preview;
import androidx.camera.lifecycle.ProcessCameraProvider;
import androidx.camera.view.PreviewView;
import androidx.core.content.ContextCompat;
import androidx.core.graphics.Insets;
import androidx.core.view.ViewCompat;
import androidx.core.view.WindowInsetsCompat;

import com.google.common.util.concurrent.ListenableFuture;
import com.google.mlkit.vision.common.InputImage;
import com.google.mlkit.vision.text.TextRecognition;
import com.google.mlkit.vision.text.TextRecognizer;
import com.google.mlkit.vision.text.latin.TextRecognizerOptions;
import com.google.mlkit.common.model.DownloadConditions;
import com.google.mlkit.nl.translate.TranslateLanguage;
import com.google.mlkit.nl.translate.Translator;
import com.google.mlkit.nl.translate.TranslatorOptions;
import com.google.mlkit.nl.translate.Translation;

import java.util.*;
import org.json.JSONObject;
import org.json.JSONArray;
import java.net.HttpURLConnection;
import java.net.URL;
import java.io.InputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import com.googlecode.tesseract.android.TessBaseAPI;
import java.nio.charset.StandardCharsets;
import android.text.InputType;
import java.util.regex.*;

/** Camera->cropped OCR->optional offline translation->speech. No screenshot storage. */
public class MainActivity extends AppCompatActivity {
    private final Handler handler = new Handler(Looper.getMainLooper());
    private final ExecutorService cameraExecutor = Executors.newSingleThreadExecutor();
    // English captions: fast Latin ML Kit. Russian captions: offline Tesseract with bundled rus.traineddata.
    private final TextRecognizer recognizer = TextRecognition.getClient(TextRecognizerOptions.DEFAULT_OPTIONS);
    private final ExecutorService russianOcrExecutor = Executors.newSingleThreadExecutor();
    private TessBaseAPI russianOcr;
    private volatile boolean russianOcrUnavailable = false;
    private long ocrModeGeneration = 0;
    private final Map<String, Boolean> characterGender = new LinkedHashMap<>();
    private final ArrayList<Voice> russianVoices = new ArrayList<>();
    private SharedPreferences prefs;
    private final LinkedHashMap<String, LinkedHashMap<String, CharacterInfo>> profiles = new LinkedHashMap<>();
    private String activeGame = "Без игры";
    private Spinner gameSpinner;
    private EditText maleNamesInput, femaleNamesInput;
    private LinearLayout[] settingsTabs;
    private boolean updatingGames = false;
    private final ExecutorService translationExecutor = Executors.newSingleThreadExecutor();
    private long translationGeneration = 0;
    private static final class CharacterInfo {
        String ru;
        boolean male;
        CharacterInfo(String ru, boolean male) { this.ru=ru; this.male=male; }
    }

    private static final class ImportedCharacter {
        String english, russian;
        // null means Wikidata supplied no reliable male/female category.
        Boolean male;
        boolean selected = true;
        ImportedCharacter(String en, String ru, Boolean gender) {
            english=en; russian=ru; male=gender;
        }
    }
    private static final String WD_API = "https://www.wikidata.org/w/api.php";
    private PreviewView preview;
    private Camera boundCamera;
    private TextView zoomLabel;
    private float cameraZoom = 1f;
    private int cameraOrientation = 0; // 0 auto, 1 portrait, 2 landscape

    private RoiOverlay overlay;
    private TextView status, recognized, speedLabel, namesLabel;
    private Spinner maleSpinner, femaleSpinner, ttsEngineSpinner;
    private final ArrayList<String> availableTtsEngines = new ArrayList<>();
    private boolean updatingTtsEngineUi = false;
    private String selectedTtsEngine = "";
    private int ttsInitGeneration = 0;
    private Switch translateSwitch;
    private Button recognitionToggle;
    private TextToSpeech tts;
    private Translator translator;
    private boolean translatorReady = false, ttsReady = false, started = false;
    private volatile boolean busy = false;
    private int attempts = 0, framesSinceText = 0;
    private String candidate = "", lastSpoken = "";
    private String candidateSpeaker = "";
    private long candidateStartedAt = 0;
    private long lastTextSeenAt = 0;
    private boolean subtitleCleared = true;
    private final Deque<SpokenRecord> recentSpeech = new ArrayDeque<>();
    private String activeSpeaker = null;
    private long activeSpeakerUntil = 0;
    private long lastSpokenAt = 0;
    private float widthFrac = .82f, heightFrac = .17f, centerYFrac = .80f, speechRate = 1.25f;
    private int maleIndex = 0, femaleIndex = 0, contrastMode = 0;
    private static final float SAME_TEXT_THRESHOLD = .12f;
    private final ActivityResultLauncher<String> cameraPermission = registerForActivityResult(new ActivityResultContracts.RequestPermission(), allowed -> {
        if (allowed) startCamera(); else show("Нужно разрешение камеры");
    });

    @Override public void onCreate(Bundle state) {
        super.onCreate(state);
        getWindow().addFlags(android.view.WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        prefs = getSharedPreferences("subtitle_voice", MODE_PRIVATE);
        widthFrac = prefs.getFloat("roiWidth", .82f);
        heightFrac = prefs.getFloat("roiHeight", .17f);
        centerYFrac = prefs.getFloat("roiCenter", .80f);
        speechRate = prefs.getFloat("speechRate", 1.25f);
        maleIndex = prefs.getInt("maleVoice", 0);
        femaleIndex = prefs.getInt("femaleVoice", 0);
        contrastMode = prefs.getInt("contrastMode", 0);
        cameraZoom = Math.max(1f, Math.min(4f, prefs.getFloat("cameraZoomV112", 1f)));
        cameraOrientation = Math.max(0, Math.min(2, prefs.getInt("cameraOrientationV112", 0)));
        applyOrientation(cameraOrientation);
        loadProfiles();
        activeGame = prefs.getString("activeGameV16", "Без игры");
        if (!profiles.containsKey(activeGame)) activeGame="Без игры";
        activateGame(activeGame);
        started=prefs.getBoolean("recognitionActiveV113",true);
        buildUi();
        selectedTtsEngine = prefs.getString("ttsEnginePackageV110", "");
        initializeTts(selectedTtsEngine);
        TranslatorOptions options = new TranslatorOptions.Builder()
            .setSourceLanguage(TranslateLanguage.ENGLISH).setTargetLanguage(TranslateLanguage.RUSSIAN).build();
        translator = Translation.getClient(options);
        if (translateSwitch.isChecked()) prepareTranslator();
        requestCamera();
    }

    private int dp(float value) { return (int)(getResources().getDisplayMetrics().density * value + .5f); }
    private TextView text(String s, int sp) { TextView t = new TextView(this); t.setText(s); t.setTextColor(Color.WHITE); t.setTextSize(sp); t.setPadding(dp(4),dp(6),dp(4),dp(6)); return t; }
    private LinearLayout.LayoutParams full() { return new LinearLayout.LayoutParams(-1, -2); }
    private void add(LinearLayout l, View v) { l.addView(v,full()); }
    private void buildUi() {
        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setBackgroundColor(Color.rgb(13,18,29));
        // Android 15+ draws application content behind the navigation bar by default.
        // Respect system bar and cutout insets so the bottom controls stay accessible.
        ViewCompat.setOnApplyWindowInsetsListener(root,(view,insets)->{
            Insets safe=insets.getInsets(WindowInsetsCompat.Type.systemBars()
                | WindowInsetsCompat.Type.displayCutout());
            view.setPadding(safe.left,safe.top,safe.right,safe.bottom);
            return insets;
        });
        TextView heading=text("SUBTITLE VOICE",20);
        heading.setGravity(Gravity.CENTER_VERTICAL);
        add(root,heading);
        LinearLayout tabBar=new LinearLayout(this);
        tabBar.setOrientation(LinearLayout.HORIZONTAL);
        add(root,tabBar);
        ScrollView scroll=new ScrollView(this);
        scroll.setFillViewport(true);
        scroll.setClipToPadding(false);
        root.addView(scroll,new LinearLayout.LayoutParams(-1,0,1));
        LinearLayout holder=new LinearLayout(this);
        holder.setOrientation(LinearLayout.VERTICAL);
        holder.setPadding(dp(12),dp(4),dp(12),dp(32));
        scroll.addView(holder);
        settingsTabs=new LinearLayout[3];
        for(int i=0;i<settingsTabs.length;i++){
            settingsTabs[i]=new LinearLayout(this);
            settingsTabs[i].setOrientation(LinearLayout.VERTICAL);
            add(holder,settingsTabs[i]);
        }
        String[] tabNames={"Общее","Голоса","Игры"};
        for(int i=0;i<tabNames.length;i++){
            final int page=i;
            Button tab=new Button(this);
            tab.setText(tabNames[i]);
            tab.setAllCaps(false);
            tabBar.addView(tab,new LinearLayout.LayoutParams(0,dp(52),1));
            tab.setOnClickListener(v->{
                for(int j=0;j<settingsTabs.length;j++)
                    settingsTabs[j].setVisibility(j==page?View.VISIBLE:View.GONE);
                scroll.scrollTo(0,0);
            });
        }
        for(int i=0;i<settingsTabs.length;i++)
            settingsTabs[i].setVisibility(i==0?View.VISIBLE:View.GONE);
        LinearLayout common=settingsTabs[0],voices=settingsTabs[1],games=settingsTabs[2];

        // General: live preview -> recognition switch -> translation switch -> frame accordion.
        FrameLayout stage=new FrameLayout(this);
        stage.setBackgroundColor(Color.BLACK);
        add(common,stage);
        stage.getLayoutParams().height=dp(getResources().getConfiguration().orientation
            == Configuration.ORIENTATION_LANDSCAPE ? 230 : 300);
        preview=new PreviewView(this);
        preview.setScaleType(PreviewView.ScaleType.FILL_CENTER);
        stage.addView(preview,new FrameLayout.LayoutParams(-1,-1));
        overlay=new RoiOverlay();
        stage.addView(overlay,new FrameLayout.LayoutParams(-1,-1));

        recognitionToggle=new Button(this);
        recognitionToggle.setAllCaps(false);
        add(common,recognitionToggle);
        updateRecognitionButton();
        recognitionToggle.setOnClickListener(v->{
            started=!started;
            prefs.edit().putBoolean("recognitionActiveV113",started).apply();
            translationGeneration++;
            candidate="";attempts=0;
            if(!started && tts!=null)tts.stop();
            updateRecognitionButton();
        });
        translateSwitch=new Switch(this);
        translateSwitch.setText("Переводить на русский");
        translateSwitch.setTextColor(Color.WHITE);
        translateSwitch.setChecked(prefs.getBoolean("translate",true));
        add(common,translateSwitch);
        translateSwitch.setOnCheckedChangeListener((button,on)->{
            prefs.edit().putBoolean("translate",on).apply();
            translationGeneration++;
            ocrModeGeneration++;
            lastSpoken="";candidate="";attempts=0;framesSinceText=0;
            subtitleCleared=true;recentSpeech.clear();
            if(tts!=null)tts.stop();
            if(on)prepareTranslator();
            if(recognized!=null)recognized.setText(on
                ? "Распознавание английского текста и перевод"
                : "Распознавание русского текста без перевода");
        });

        boolean expanded=prefs.getBoolean("frameSettingsExpandedV113",false);
        Button frameSettingsToggle=new Button(this);
        frameSettingsToggle.setAllCaps(false);
        frameSettingsToggle.setText(expanded?"▾  Настройки рамки и камеры":"▸  Настройки рамки и камеры");
        add(common,frameSettingsToggle);
        LinearLayout frameSettings=new LinearLayout(this);
        frameSettings.setOrientation(LinearLayout.VERTICAL);
        frameSettings.setPadding(dp(4),0,dp(4),dp(8));
        frameSettings.setVisibility(expanded?View.VISIBLE:View.GONE);
        add(common,frameSettings);
        frameSettingsToggle.setOnClickListener(v->{
            boolean nowExpanded=frameSettings.getVisibility()!=View.VISIBLE;
            frameSettings.setVisibility(nowExpanded?View.VISIBLE:View.GONE);
            frameSettingsToggle.setText(nowExpanded
                ?"▾  Настройки рамки и камеры":"▸  Настройки рамки и камеры");
            prefs.edit().putBoolean("frameSettingsExpandedV113",nowExpanded).apply();
        });
        add(frameSettings,text("Ориентация камеры",14));
        Spinner orientationSpinner=new Spinner(this);
        orientationSpinner.setAdapter(new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,
            new String[]{"Авто (поворот телефона)","Вертикально","Горизонтально"}));
        orientationSpinner.setSelection(cameraOrientation);
        add(frameSettings,orientationSpinner);
        orientationSpinner.setOnItemSelectedListener(new SpinnerListener(i->{
            if(cameraOrientation!=i){
                cameraOrientation=i;
                prefs.edit().putInt("cameraOrientationV112",i).apply();
                applyOrientation(i);
            }
        }));
        zoomLabel=text("Приближение камеры: "+String.format(Locale.US,"%.1f×",cameraZoom),14);
        add(frameSettings,zoomLabel);
        SeekBar cameraZoomBar=new SeekBar(this);
        cameraZoomBar.setMax(300);
        cameraZoomBar.setProgress(Math.round((cameraZoom-1f)*100f));
        add(frameSettings,cameraZoomBar);
        cameraZoomBar.setOnSeekBarChangeListener(new SimpleSeekListener(v->{
            cameraZoom=1f+v/100f;
            prefs.edit().putFloat("cameraZoomV112",cameraZoom).apply();
            applyCameraZoom();
        }));
        add(frameSettings,text("Обработка изображения",14));
        Spinner contrastSpinner=new Spinner(this);
        contrastSpinner.setAdapter(new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,
            new String[]{"HD без фильтра","Светлые буквы","Тёмные буквы"}));
        contrastSpinner.setSelection(contrastMode);
        add(frameSettings,contrastSpinner);
        contrastSpinner.setOnItemSelectedListener(new SpinnerListener(i->{
            contrastMode=i;prefs.edit().putInt("contrastMode",i).apply();
        }));
        addSlider(frameSettings,"Ширина рамки",55,100,Math.round(widthFrac*100),v->{widthFrac=v/100f;saveRoi();});
        addSlider(frameSettings,"Высота рамки",7,35,Math.round(heightFrac*100),v->{heightFrac=v/100f;saveRoi();});
        addSlider(frameSettings,"Положение по вертикали",55,95,Math.round(centerYFrac*100),v->{centerYFrac=v/100f;saveRoi();});
        status=text("Инициализация камеры…",13);
        add(common,status);
        recognized=text("Последняя реплика: —",14);
        add(common,recognized);

        // Voices: synthesizer, male/female voice models and speed, with no game management.
        add(voices,text("Движок озвучки",17));
        ttsEngineSpinner=new Spinner(this);add(voices,ttsEngineSpinner);
        Button scanTts=new Button(this);scanTts.setText("Обновить движки");add(voices,scanTts);
        scanTts.setOnClickListener(v->refreshTtsEngines());
        Button ttsSettings=new Button(this);
        ttsSettings.setText("Настройки голосов Android");add(voices,ttsSettings);
        ttsSettings.setOnClickListener(v->{
            try{startActivity(new Intent("android.settings.TTS_SETTINGS"));}
            catch(Exception e){show("Настройки TTS можно открыть в настройках телефона");}
        });
        add(voices,text("Мужской голос",14));
        maleSpinner=new Spinner(this);add(voices,maleSpinner);
        Button testM=new Button(this);testM.setText("Проверить мужской голос");add(voices,testM);
        testM.setOnClickListener(v->speak("Привет! Это пример мужского голоса.",true));
        add(voices,text("Женский голос",14));
        femaleSpinner=new Spinner(this);add(voices,femaleSpinner);
        Button testF=new Button(this);testF.setText("Проверить женский голос");add(voices,testF);
        testF.setOnClickListener(v->speak("Привет! Это пример женского голоса.",false));
        speedLabel=text("Скорость речи: "+String.format(Locale.US,"%.2f×",speechRate),16);
        add(voices,speedLabel);
        SeekBar speechSlider=new SeekBar(this);
        speechSlider.setMax(130);
        speechSlider.setProgress(Math.round((speechRate-.7f)*100));
        add(voices,speechSlider);
        speechSlider.setOnSeekBarChangeListener(new SimpleSeekListener(v->{
            speechRate=.7f+v/100f;
            speedLabel.setText("Скорость речи: "+String.format(Locale.US,"%.2f×",speechRate));
            prefs.edit().putFloat("speechRate",speechRate).apply();
            if(ttsReady && tts!=null)tts.setSpeechRate(speechRate);
        }));
        add(voices,text("Персонаж без назначенного голоса всегда говорит мужским. Для дополнительных офлайн-голосов можно установить совместимый TTS-движок.",13));

        // Games: a separate page for profiles, character genders and on-demand import.
        add(games,text("Профиль игры",17));
        gameSpinner=new Spinner(this);add(games,gameSpinner);
        refreshGameSpinner();
        gameSpinner.setOnItemSelectedListener(new SpinnerListener(i->{
            if(updatingGames||i<0||i>=profiles.size())return;
            String selected=new ArrayList<>(profiles.keySet()).get(i);
            if(!selected.equals(activeGame)){
                activeGame=selected;activateGame(activeGame);
                translationGeneration++;renderNames();
            }
        }));
        EditText gameInput=new EditText(this);
        gameInput.setSingleLine(true);gameInput.setTextColor(Color.WHITE);
        gameInput.setHint("Новая игра, например Final Fantasy VII");
        add(games,gameInput);
        Button addGame=new Button(this);addGame.setText("Создать / выбрать игру");add(games,addGame);
        addGame.setOnClickListener(v->{
            String game=gameInput.getText().toString().trim();if(game.isEmpty())return;
            profiles.putIfAbsent(game,new LinkedHashMap<>());
            activeGame=game;activateGame(game);
            saveProfiles();refreshGameSpinner();renderNames();gameInput.setText("");
            translationGeneration++;
        });
        add(games,text("Мужские персонажи (через запятую)",14));
        maleNamesInput=new EditText(this);maleNamesInput.setTextColor(Color.WHITE);
        maleNamesInput.setHint("Cloud=Клауд, Barret=Баррет");maleNamesInput.setMinLines(2);
        add(games,maleNamesInput);
        add(games,text("Женские персонажи (через запятую)",14));
        femaleNamesInput=new EditText(this);femaleNamesInput.setTextColor(Color.WHITE);
        femaleNamesInput.setHint("Tifa=Тифа, Aerith=Айрис");femaleNamesInput.setMinLines(2);
        add(games,femaleNamesInput);
        add(games,text("Формат: Имя=Русское произношение. Списки сохраняются для выбранной игры.",13));
        Button importGame=new Button(this);
        importGame.setText("Найти персонажей игры в интернете");add(games,importGame);
        importGame.setOnClickListener(v->{
            String game=gameInput.getText().toString().trim();
            if(game.isEmpty())game=activeGame;
            if(game.equals("Без игры")){
                Toast.makeText(this,"Сначала выбери или создай игру",Toast.LENGTH_SHORT).show();return;
            }
            importCharactersFromWikidata(game,importGame);
        });
        Button saveNames=new Button(this);
        saveNames.setText("Сохранить имена персонажей");add(games,saveNames);
        saveNames.setOnClickListener(v->saveCommaSeparatedNames());
        Button removeGame=new Button(this);
        removeGame.setText("Удалить выбранный профиль");add(games,removeGame);
        removeGame.setOnClickListener(v->{
            if("Без игры".equals(activeGame))return;
            profiles.remove(activeGame);activeGame="Без игры";
            activateGame(activeGame);saveProfiles();refreshGameSpinner();renderNames();
            translationGeneration++;
        });
        namesLabel=text("",12);add(games,namesLabel);renderNames();
        setContentView(root);
        ViewCompat.requestApplyInsets(root);
    }

    private void updateRecognitionButton(){
        if(recognitionToggle!=null)recognitionToggle.setText(started
            ?"Остановить распознавание":"Включить распознавание");
    }

    private String formattedNames(boolean male){
        LinkedHashMap<String,CharacterInfo> list=profiles.get(activeGame);
        ArrayList<String> names=new ArrayList<>();
        if(list!=null)for(Map.Entry<String,CharacterInfo> e:list.entrySet()){
            CharacterInfo info=e.getValue();if(info.male!=male)continue;
            names.add(e.getKey().equals(info.ru)?e.getKey():e.getKey()+"="+info.ru);
        }
        return String.join(", ",names);
    }
    private void saveCommaSeparatedNames(){
        LinkedHashMap<String,CharacterInfo> list=new LinkedHashMap<>();
        parseCommaNames(maleNamesInput.getText().toString(),true,list);
        parseCommaNames(femaleNamesInput.getText().toString(),false,list);
        profiles.put(activeGame,list);activateGame(activeGame);saveProfiles();renderNames();
        Toast.makeText(this,"Имена сохранены: "+list.size(),Toast.LENGTH_SHORT).show();
    }
    private void parseCommaNames(String source,boolean male,LinkedHashMap<String,CharacterInfo> target){
        for(String token:source.split("[,\n;]+")){
            String entry=token.trim();if(entry.isEmpty())continue;
            String[] pair=entry.split("=",2);
            String en=pair[0].trim();if(en.isEmpty())continue;
            String ru=pair.length>1?pair[1].trim():"";
            CharacterInfo previous=profiles.get(activeGame).get(en);
            if(ru.isEmpty())ru=previous!=null?previous.ru:en;
            target.put(en,new CharacterInfo(ru,male));
        }
    }
    private interface SliderAction {void update(int value);}
    private static class SimpleSeekListener implements SeekBar.OnSeekBarChangeListener {
        final SliderAction action;SimpleSeekListener(SliderAction a){action=a;}
        public void onProgressChanged(SeekBar bar,int progress,boolean fromUser){if(fromUser)action.update(progress);}
        public void onStartTrackingTouch(SeekBar bar){} public void onStopTrackingTouch(SeekBar bar){}
    }
    private interface SelectAction {void selected(int n);}
    private static class SpinnerListener implements AdapterView.OnItemSelectedListener {
        final SelectAction action;SpinnerListener(SelectAction a){action=a;}
        public void onItemSelected(AdapterView<?> p,View v,int pos,long id){action.selected(pos);}
        public void onNothingSelected(AdapterView<?> p){}
    }
    private void addSlider(LinearLayout layout,String label,int min,int max,int initial,SliderAction action) {
        TextView t=text(label+": "+initial+"%",12);add(layout,t);
        SeekBar bar=new SeekBar(this);bar.setMax(max-min);bar.setProgress(Math.max(0,Math.min(max-min,initial-min)));add(layout,bar);
        bar.setOnSeekBarChangeListener(new SimpleSeekListener(n->{t.setText(label+": "+(n+min)+"%");action.update(n+min);overlay.invalidate();}));
    }
    private void saveRoi() { prefs.edit().putFloat("roiWidth",widthFrac).putFloat("roiHeight",heightFrac).putFloat("roiCenter",centerYFrac).apply(); }
    private void show(String message) { if(status!=null)status.setText(message); }
    private void loadProfiles(){
        profiles.put("Без игры", new LinkedHashMap<>());
        try{
            String json=prefs.getString("gameProfilesV16", "");
            if(!json.isEmpty()){
                JSONObject root=new JSONObject(json);
                Iterator<String> games=root.keys();
                while(games.hasNext()){
                    String game=games.next();JSONObject obj=root.getJSONObject(game);
                    LinkedHashMap<String,CharacterInfo> list=new LinkedHashMap<>();
                    Iterator<String> names=obj.keys();
                    while(names.hasNext()){
                        String alias=names.next();JSONObject c=obj.getJSONObject(alias);
                        list.put(alias,new CharacterInfo(c.optString("ru",alias),c.optBoolean("male",true)));
                    }
                    profiles.put(game,list);
                }
                return;
            }
        }catch(Exception ignored){}
        // Migrate old global speaker list once, without losing it on upgrade.
        String raw=prefs.getString("characters","Вася|1;Петя|1;Маша|0;Марина|0");
        for(String item:raw.split(";")){
            String[] pair=item.split("\\|",2);
            if(pair.length==2)profiles.get("Без игры").put(pair[0],new CharacterInfo(pair[0],"1".equals(pair[1])));
        }
        saveProfiles();
    }
    private void activateGame(String game){
        characterGender.clear();
        LinkedHashMap<String,CharacterInfo> list=profiles.get(game);
        if(list!=null)for(Map.Entry<String,CharacterInfo> e:list.entrySet())characterGender.put(e.getKey().toLowerCase(Locale.ROOT),e.getValue().male);
        prefs.edit().putString("activeGameV16",game).apply();
    }
    private void refreshGameSpinner(){
        if(gameSpinner==null)return;
        updatingGames=true;
        ArrayList<String> names=new ArrayList<>(profiles.keySet());
        gameSpinner.setAdapter(new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,names));
        gameSpinner.setSelection(Math.max(0,names.indexOf(activeGame)));
        updatingGames=false;
    }
    private void saveProfiles(){
        try{
            JSONObject obj=new JSONObject();
            for(Map.Entry<String,LinkedHashMap<String,CharacterInfo>> game:profiles.entrySet()){
                JSONObject chars=new JSONObject();
                for(Map.Entry<String,CharacterInfo> e:game.getValue().entrySet()){
                    JSONObject c=new JSONObject();c.put("ru",e.getValue().ru);c.put("male",e.getValue().male);chars.put(e.getKey(),c);
                }
                obj.put(game.getKey(),chars);
            }
            prefs.edit().putString("gameProfilesV16",obj.toString()).apply();
        }catch(Exception ignored){}
    }
    /** Wikidata import is an explicit, one-shot user action. Never runs in the recognition loop. */
    private void importCharactersFromWikidata(String requestedGame, Button button) {
        button.setEnabled(false);
        String originalLabel=button.getText().toString();
        button.setText("Загрузка списка персонажей…");
        translationExecutor.execute(() -> {
            try {
                ArrayList<ImportedCharacter> found=fetchGameCharacters(requestedGame);
                handler.post(() -> {
                    button.setEnabled(true);button.setText(originalLabel);
                    if(found.isEmpty()){
                        new AlertDialog.Builder(this)
                            .setTitle("Персонажи не найдены")
                            .setMessage("В Wikidata нет привязанного списка персонажей для «"+requestedGame+"» или данные неполные. Можно добавить имена вручную. Это не ошибка офлайн-распознавания.")
                            .setPositiveButton("Понятно",(d,w)->{}).show();
                    } else showImportReview(requestedGame,found);
                });
            } catch(Exception ex) {
                handler.post(() -> {button.setEnabled(true);button.setText(originalLabel);
                    new AlertDialog.Builder(this).setTitle("Не получилось загрузить список")
                        .setMessage("Проверь интернет или название игры. Подробности: "+ex.getMessage())
                        .setPositiveButton("ОК",(d,w)->{}).show();
                });
            }
        });
    }

    private JSONObject wikidataGet(String params) throws Exception {
        URL url=new URL(WD_API+"?format=json&"+params);
        HttpURLConnection c=(HttpURLConnection)url.openConnection();
        c.setConnectTimeout(6500);c.setReadTimeout(7500);
        c.setRequestProperty("User-Agent","SubtitleVoice/1.7 (Android personal offline subtitle assistant; Wikidata character import)");
        c.setRequestProperty("Accept","application/json");
        try {
            if(c.getResponseCode()!=200)throw new Exception("Wikidata HTTP "+c.getResponseCode());
            try(InputStream in=c.getInputStream();ByteArrayOutputStream data=new ByteArrayOutputStream()) {
                byte[] buf=new byte[8192];int count;
                while((count=in.read(buf))!=-1){ data.write(buf,0,count); if(data.size()>1500000)throw new Exception("Слишком большой ответ"); }
                return new JSONObject(data.toString("UTF-8"));
            }
        } finally {c.disconnect();}
    }
    private String encode(String s) throws Exception {return URLEncoder.encode(s,"UTF-8");}
    private String label(JSONObject entity,String lang) {
        return entity.optJSONObject("labels") == null ? "" :
            entity.optJSONObject("labels").optJSONObject(lang) == null ? "" :
            entity.optJSONObject("labels").optJSONObject(lang).optString("value", "");
    }
    private String claimEntityId(JSONObject entity,String property) {
        JSONArray a=entity.optJSONObject("claims")==null?null:entity.optJSONObject("claims").optJSONArray(property);
        if(a==null||a.length()==0)return "";
        JSONObject snak=a.optJSONObject(0)==null?null:a.optJSONObject(0).optJSONObject("mainsnak");
        JSONObject value=snak==null||snak.optJSONObject("datavalue")==null?null:snak.optJSONObject("datavalue").optJSONObject("value");
        return value==null?"":value.optString("id","");
    }
    private ArrayList<ImportedCharacter> fetchGameCharacters(String game) throws Exception {
        JSONObject search=wikidataGet("action=wbsearchentities&language=en&type=item&limit=8&search="+encode(game));
        JSONArray hits=search.optJSONArray("search");
        if(hits==null||hits.length()==0)return new ArrayList<>();
        LinkedHashSet<String> ids=new LinkedHashSet<>();
        for(int i=0;i<hits.length();i++){
            JSONObject item=hits.optJSONObject(i);
            if(item!=null && item.optString("id").matches("Q[0-9]+"))ids.add(item.optString("id"));
        }
        JSONObject games=wikidataGet("action=wbgetentities&props=claims%7Clabels&languages=en%7Cru&ids="+encode(String.join("|",ids)));
        JSONObject gameEntities=games.optJSONObject("entities");
        if(gameEntities==null)return new ArrayList<>();
        LinkedHashSet<String> characterIds=new LinkedHashSet<>();
        for(String id:ids){
            JSONObject entity=gameEntities.optJSONObject(id);
            if(entity==null)continue;
            String gameLabel=label(entity,"en");
            // Avoid accidentally importing a similarly named film/novel/game.
            if(gameLabel.isEmpty() || !(gameLabel.equalsIgnoreCase(game)||gameLabel.toLowerCase(Locale.ROOT).contains(game.toLowerCase(Locale.ROOT))
                ||game.toLowerCase(Locale.ROOT).contains(gameLabel.toLowerCase(Locale.ROOT))))continue;
            JSONObject claims=entity.optJSONObject("claims");
            JSONArray characters=claims==null?null:claims.optJSONArray("P674"); // characters
            if(characters==null)continue;
            for(int i=0;i<characters.length()&&characterIds.size()<150;i++){
                JSONObject statement=characters.optJSONObject(i);
                JSONObject snak=statement==null?null:statement.optJSONObject("mainsnak");
                JSONObject val=snak==null?null:snak.optJSONObject("datavalue");
                JSONObject obj=val==null?null:val.optJSONObject("value");
                String charId=obj==null?"":obj.optString("id","");
                if(charId.matches("Q[0-9]+"))characterIds.add(charId);
            }
            if(!characterIds.isEmpty())break;
        }
        ArrayList<ImportedCharacter> result=new ArrayList<>();
        if(characterIds.isEmpty())return result;
        ArrayList<String> allIds=new ArrayList<>(characterIds);
        for(int start=0;start<allIds.size();start+=35){
            String batch=String.join("|",allIds.subList(start,Math.min(start+35,allIds.size())));
            JSONObject response=wikidataGet("action=wbgetentities&props=claims%7Clabels&languages=en%7Cru&ids="+encode(batch));
            JSONObject characters=response.optJSONObject("entities");
            if(characters==null)continue;
            for(String id:allIds.subList(start,Math.min(start+35,allIds.size()))){
                JSONObject item=characters.optJSONObject(id);if(item==null)continue;
                String en=label(item,"en"), ru=label(item,"ru");
                if(en.isEmpty())continue;
                if(ru.isEmpty())ru=en; // no guessing a transliteration
                String gender=claimEntityId(item,"P21");
                Boolean male=gender.equals("Q6581097")?Boolean.TRUE:
                    gender.equals("Q6581072")?Boolean.FALSE:null;
                result.add(new ImportedCharacter(en,ru,male));
            }
        }
        result.sort((a,b)->a.english.compareToIgnoreCase(b.english));
        return result;
    }
    private void showImportReview(String game,ArrayList<ImportedCharacter> characters){
        ScrollView scroll=new ScrollView(this);
        LinearLayout content=new LinearLayout(this);content.setPadding(dp(12),dp(8),dp(12),dp(8));
        content.setOrientation(LinearLayout.VERTICAL);scroll.addView(content);
        TextView intro=text("Проверь найденные имена и произношения. Пол без подтверждения источника отмечен как «Неизвестно» — выбери голос вручную. Снятие галочки исключает персонажа.",13);
        intro.setTextColor(Color.BLACK);add(content,intro);
        ArrayList<CheckBox> checks=new ArrayList<>();
        ArrayList<EditText> names=new ArrayList<>();
        ArrayList<Spinner> genders=new ArrayList<>();
        for(ImportedCharacter item:characters){
            CheckBox box=new CheckBox(this);box.setText(item.english);
            box.setTextColor(Color.BLACK);box.setChecked(true);add(content,box);checks.add(box);
            EditText russian=new EditText(this);russian.setText(item.russian);
            russian.setSingleLine(true);russian.setTextColor(Color.BLACK);russian.setHint("Произношение по-русски");add(content,russian);names.add(russian);
            Spinner gender=new Spinner(this);
            gender.setAdapter(new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,
                new String[]{"Мужской голос","Женский голос","Неизвестно — не импортировать"}));
            gender.setSelection(item.male==null?2:(item.male?0:1));add(content,gender);genders.add(gender);
        }
        new AlertDialog.Builder(this).setTitle("Персонажи: "+game+" ("+characters.size()+")")
            .setView(scroll)
            .setNegativeButton("Отмена",(d,w)->{})
            .setPositiveButton("Добавить в поля",(d,w)->{
                if(!profiles.containsKey(game))profiles.put(game,new LinkedHashMap<>());
                activeGame=game;activateGame(game);saveProfiles();refreshGameSpinner();renderNames();
                ArrayList<String> male=new ArrayList<>(),female=new ArrayList<>();
                for(int i=0;i<characters.size();i++){
                    if(!checks.get(i).isChecked()||genders.get(i).getSelectedItemPosition()==2)continue;
                    String ru=names.get(i).getText().toString().trim();
                    String en=characters.get(i).english;
                    if(en.isEmpty())continue;
                    String item=ru.isEmpty()||en.equals(ru)?en:en+"="+ru;
                    (genders.get(i).getSelectedItemPosition()==0?male:female).add(item);
                }
                appendNames(maleNamesInput,male);
                appendNames(femaleNamesInput,female);
                Toast.makeText(this,"Проверь поля и нажми «Сохранить мужские и женские имена»",Toast.LENGTH_LONG).show();
            }).show();
    }

    private void appendNames(EditText field,ArrayList<String> items){
        if(items.isEmpty())return;
        String old=field.getText().toString().trim();
        field.setText(old+(old.isEmpty()?"":", ")+String.join(", ",items));
    }

    private void renderNames(){
        if(namesLabel==null)return;
        StringBuilder b=new StringBuilder();
        LinkedHashMap<String,CharacterInfo> list=profiles.get(activeGame);
        if(list!=null)for(Map.Entry<String,CharacterInfo> e:list.entrySet()){
            if(b.length()>0)b.append("\n");
            b.append(e.getKey()).append(" → ").append(e.getValue().ru).append(" (" ).append(e.getValue().male?"муж.":"жен.").append(")");
        }
        namesLabel.setText(b.length()==0?"В этой игре пока нет персонажей":b.toString());
        if(maleNamesInput!=null)maleNamesInput.setText(formattedNames(true));
        if(femaleNamesInput!=null)femaleNamesInput.setText(formattedNames(false));
    }
    // Sort longest names first so Cloud Strife is substituted before Cloud.
    private String protectNames(String english){
        LinkedHashMap<String,CharacterInfo> list=profiles.get(activeGame);
        if(list==null)return english;
        List<String> names=new ArrayList<>(list.keySet());names.sort((a,b)->Integer.compare(b.length(),a.length()));
        String output=english;
        for(String name:names){
            if(name.isEmpty())continue;
            output=Pattern.compile("(?<![\\p{L}\\p{N}])"+Pattern.quote(name)+"(?![\\p{L}\\p{N}])",Pattern.CASE_INSENSITIVE|Pattern.UNICODE_CASE)
                .matcher(output).replaceAll(Matcher.quoteReplacement(list.get(name).ru));
        }
        return output;
    }
    private String glossary(){
        LinkedHashMap<String,CharacterInfo> list=profiles.get(activeGame);
        if(list==null||list.isEmpty())return "(нет)";
        StringBuilder b=new StringBuilder();
        for(Map.Entry<String,CharacterInfo> e:list.entrySet())b.append(e.getKey()).append(" = ").append(e.getValue().ru).append("; ");
        return b.toString();
    }
    private void translateOrRead(String input, java.util.function.Consumer<String> success,
                                 java.util.function.Consumer<String> failure) {
        if(input==null || input.trim().isEmpty())return;
        if(!translateSwitch.isChecked()) {
            success.accept(input); // Russian OCR -> original Russian text, NEVER translate.
            return;
        }
        if(!translatorReady){failure.accept("Ожидаю загрузку офлайн-переводчика");return;}
        // The only translation path is free ML Kit running on the phone.
        translator.translate(protectNames(input))
            .addOnSuccessListener(success::accept)
            .addOnFailureListener(e->failure.accept(e.getMessage()));
    }
    /** Switches the Android speech service without restarting the camera or translator.
     *  Only TTS engines installed by the user can be selected; the app uses no cloud speech API.
     */
    private void initializeTts(String packageName) {
        final int generation = ++ttsInitGeneration;
        ttsReady=false;
        selectedTtsEngine=packageName == null ? "" : packageName;
        if (tts!=null) {
            tts.stop();
            tts.shutdown();
            tts=null;
        }
        russianVoices.clear();
        TextToSpeech.OnInitListener callback = code -> handler.post(() -> {
            if (isFinishing() || isDestroyed() || generation!=ttsInitGeneration) return;
            ttsReady=code==TextToSpeech.SUCCESS;
            if (ttsReady && tts!=null) {
                tts.setLanguage(new Locale("ru","RU"));
                tts.setSpeechRate(speechRate);
                refreshTtsEngines();
                populateVoices();
            } else {
                refreshTtsEngines();
                show("Не удалось запустить выбранный TTS-движок. Проверь его установку и языковые модели.");
            }
        });
        tts=selectedTtsEngine.isEmpty()
            ? new TextToSpeech(this,callback)
            : new TextToSpeech(this,callback,selectedTtsEngine);
    }

    private String ttsEnginePreferenceKey(String suffix){
        return "offlineTts_"+(selectedTtsEngine.isEmpty()?"system":selectedTtsEngine)+"_"+suffix;
    }

    private void refreshTtsEngines(){
        if(ttsEngineSpinner==null || tts==null)return;
        ArrayList<String> labels=new ArrayList<>();
        availableTtsEngines.clear();
        availableTtsEngines.add("");
        labels.add("Системный движок Android");
        try {
            List<TextToSpeech.EngineInfo> installed=tts.getEngines();
            if(installed!=null)for(TextToSpeech.EngineInfo info:installed){
                if(info.name==null || info.name.trim().isEmpty())continue;
                availableTtsEngines.add(info.name);
                String title=info.label==null || info.label.trim().isEmpty()?info.name:info.label;
                labels.add(title+" ("+info.name+")");
            }
        }catch(Exception ignored){}
        int selected=Math.max(0,availableTtsEngines.indexOf(selectedTtsEngine));
        updatingTtsEngineUi=true;
        ttsEngineSpinner.setAdapter(new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,labels));
        ttsEngineSpinner.setSelection(selected);
        ttsEngineSpinner.setOnItemSelectedListener(new SpinnerListener(position->{
            if(updatingTtsEngineUi || position<0 || position>=availableTtsEngines.size())return;
            String next=availableTtsEngines.get(position);
            if(next.equals(selectedTtsEngine))return;
            prefs.edit().putString("ttsEnginePackageV110",next).apply();
            initializeTts(next);
        }));
        updatingTtsEngineUi=false;
    }

    private int storedVoiceIndex(boolean male){
        if(russianVoices.isEmpty())return 0;
        String key=ttsEnginePreferenceKey(male?"maleName":"femaleName");
        String name=prefs.getString(key,"");
        for(int i=0;i<russianVoices.size();i++)if(russianVoices.get(i).getName().equals(name))return i+1;
        // Migrate previously selected system voices only; engine-specific voices
        // must not inherit an unrelated numeric index from the old TTS engine.
        if(selectedTtsEngine.isEmpty() && !prefs.contains(key)){
            int old=male?maleIndex:femaleIndex;
            if(old>0 && old<=russianVoices.size())return old;
        }
        // Engine metadata does not explicitly carry gender. Prefer recognizable
        // Russian male/female model names when no personal choice was saved.
        String[] preferred=male
            ? new String[]{"denis","dmitri","ruslan","yuriy","aleksey","alexey","pavel","seva","artem","igor"}
            : new String[]{"irina","anna","luka","alina","elena","maria","tatyana","tatiana","natalia"};
        for(String hint:preferred){
            for(int i=0;i<russianVoices.size();i++){
                if(russianVoices.get(i).getName().toLowerCase(Locale.ROOT).contains(hint))return i+1;
            }
        }
        return 0;
    }

    private void populateVoices(){
        russianVoices.clear();
        if(tts==null || !ttsReady || maleSpinner==null || femaleSpinner==null)return;
        try {
            Set<Voice> installed=tts.getVoices();
            if(installed!=null)for(Voice v:installed){
                if(v!=null && v.getLocale()!=null &&
                   "ru".equals(v.getLocale().getLanguage()) &&
                   !v.isNetworkConnectionRequired())russianVoices.add(v);
            }
        }catch(Exception ex){show("Не получилось прочитать голоса TTS: "+ex.getMessage());}
        russianVoices.sort(Comparator.comparing(Voice::getName));
        List<String> titles=new ArrayList<>();
        titles.add("Автоматически: первый офлайн-голос RU");
        for(Voice v:russianVoices)titles.add(v.getName()+" (офлайн)");
        maleSpinner.setAdapter(new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,titles));
        femaleSpinner.setAdapter(new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,titles));
        maleSpinner.setSelection(storedVoiceIndex(true));
        femaleSpinner.setSelection(storedVoiceIndex(false));
        maleSpinner.setOnItemSelectedListener(new SpinnerListener(n->{
            maleIndex=n;
            String name=n>0 && n<=russianVoices.size()?russianVoices.get(n-1).getName():"";
            prefs.edit().putString(ttsEnginePreferenceKey("maleName"),name).putInt("maleVoice",n).apply();
        }));
        femaleSpinner.setOnItemSelectedListener(new SpinnerListener(n->{
            femaleIndex=n;
            String name=n>0 && n<=russianVoices.size()?russianVoices.get(n-1).getName():"";
            prefs.edit().putString(ttsEnginePreferenceKey("femaleName"),name).putInt("femaleVoice",n).apply();
        }));
        if(russianVoices.isEmpty())show("В выбранном движке нет скачанных офлайн-голосов RU. Установи модель русского голоса в приложении движка.");
    }
    private void prepareTranslator(){
        if(translatorReady)return;
        translator.downloadModelIfNeeded(new DownloadConditions.Builder().build())
          .addOnSuccessListener(v->{translatorReady=true;lastSpoken="";})
          .addOnFailureListener(e->show("Не удалось скачать модель перевода: "+e.getMessage()));
    }
    private void requestCamera() {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) startCamera();
        else cameraPermission.launch(Manifest.permission.CAMERA);
    }
    private void applyOrientation(int mode) {
        int target = mode==1 ? ActivityInfo.SCREEN_ORIENTATION_SENSOR_PORTRAIT
            : mode==2 ? ActivityInfo.SCREEN_ORIENTATION_SENSOR_LANDSCAPE
            : ActivityInfo.SCREEN_ORIENTATION_FULL_SENSOR;
        if(getRequestedOrientation()!=target) setRequestedOrientation(target);
    }

    private void applyCameraZoom() {
        if(boundCamera==null) {
            if(zoomLabel!=null)zoomLabel.setText("Приближение камеры: "+String.format(Locale.US,"%.1f×",cameraZoom));
            return;
        }
        ZoomState state=boundCamera.getCameraInfo().getZoomState().getValue();
        float minimum=state!=null?state.getMinZoomRatio():1f;
        float maximum=state!=null?state.getMaxZoomRatio():1f;
        float actual=Math.max(minimum,Math.min(cameraZoom,maximum));
        if(zoomLabel!=null)zoomLabel.setText("Приближение камеры: "+String.format(Locale.US,"%.1f×",actual));
        boundCamera.getCameraControl().setZoomRatio(actual);
    }

    private void startCamera(){
        if(preview==null) return;
        if(preview.getWidth()==0 || preview.getHeight()==0 || preview.getDisplay()==null) {
            preview.post(() -> {if(!isFinishing())startCamera();});
            return;
        }
        ListenableFuture<ProcessCameraProvider> future=ProcessCameraProvider.getInstance(this);
        future.addListener(()->{
            try{
                if(isFinishing())return;
                ProcessCameraProvider provider=future.get();
                provider.unbindAll();
                int displayRotation=preview.getDisplay().getRotation();
                boolean horizontal=displayRotation==Surface.ROTATION_90 || displayRotation==Surface.ROTATION_270;
                Size targetSize=new Size(horizontal ? 1920 : 1080, horizontal ? 1080 : 1920);
                Preview p=new Preview.Builder().setTargetRotation(displayRotation).build();
                p.setSurfaceProvider(preview.getSurfaceProvider());
                ImageAnalysis analysis = new ImageAnalysis.Builder()
                    .setTargetResolution(targetSize)
                    .setTargetRotation(displayRotation)
                    .setOutputImageFormat(ImageAnalysis.OUTPUT_IMAGE_FORMAT_RGBA_8888)
                    .setBackpressureStrategy(ImageAnalysis.STRATEGY_KEEP_ONLY_LATEST)
                    .build();
                // A common ViewPort makes the OCR bitmap correspond to the green preview frame.
                ViewPort viewPort=preview.getViewPort();
                final boolean viewportMapped=viewPort!=null;
                analysis.setAnalyzer(cameraExecutor, frame -> {
                    if (!started || busy) {frame.close();return;}
                    busy=true;
                    Bitmap full=null,viewportBitmap=null,oriented=null;
                    try {
                        full=bitmapFromFrame(frame);
                        viewportBitmap=full;
                        if(viewportMapped) {
                            Rect c=frame.getCropRect();
                            int left=Math.max(0,Math.min(full.getWidth()-1,c.left));
                            int top=Math.max(0,Math.min(full.getHeight()-1,c.top));
                            int cw=Math.min(full.getWidth()-left,c.width());
                            int ch=Math.min(full.getHeight()-top,c.height());
                            if(cw>0 && ch>0 && (cw!=full.getWidth() || ch!=full.getHeight()))
                                viewportBitmap=Bitmap.createBitmap(full,left,top,cw,ch);
                        }
                        int rotation=frame.getImageInfo().getRotationDegrees();
                        oriented=viewportBitmap;
                        if(rotation!=0){
                            Matrix rotate=new Matrix(); rotate.postRotate(rotation);
                            oriented=Bitmap.createBitmap(viewportBitmap,0,0,
                                viewportBitmap.getWidth(),viewportBitmap.getHeight(),rotate,true);
                        }
                        Bitmap cropped=cropToOverlay(oriented,viewportMapped);
                        if(cropped==null){busy=false;return;}
                        runOnUiThread(()->recognizeFrame(cropped));
                    }catch(Exception e){
                        busy=false;
                        runOnUiThread(()->show("Ошибка кадра: "+e.getMessage()));
                    }finally{
                        frame.close();
                        if(oriented!=null && oriented!=viewportBitmap && oriented!=full)oriented.recycle();
                        if(viewportBitmap!=null && viewportBitmap!=full)viewportBitmap.recycle();
                        if(full!=null)full.recycle();
                    }
                });
                if(viewportMapped){
                    UseCaseGroup group=new UseCaseGroup.Builder()
                        .addUseCase(p).addUseCase(analysis).setViewPort(viewPort).build();
                    boundCamera=provider.bindToLifecycle(this,CameraSelector.DEFAULT_BACK_CAMERA,group);
                }else{
                    boundCamera=provider.bindToLifecycle(this,CameraSelector.DEFAULT_BACK_CAMERA,p,analysis);
                }
                applyCameraZoom();
                updateRecognitionButton();
                show("Камера Full HD запущена (если поддерживается устройством)");
            }catch(Exception ex){show("Ошибка камеры: "+ex.getMessage());}
        }, ContextCompat.getMainExecutor(this));
    }
    private Bitmap bitmapFromFrame(ImageProxy frame){
        ImageProxy.PlaneProxy plane=frame.getPlanes()[0];
        int w=frame.getWidth(), h=frame.getHeight();
        int rowStride=plane.getRowStride();
        ByteBuffer buffer=plane.getBuffer();
        byte[] rgba=new byte[w*h*4];
        for(int row=0;row<h;row++){
            buffer.position(row*rowStride);
            buffer.get(rgba,row*w*4,w*4);
        }
        Bitmap bitmap=Bitmap.createBitmap(w,h,Bitmap.Config.ARGB_8888);
        bitmap.copyPixelsFromBuffer(ByteBuffer.wrap(rgba));
        return bitmap;
    }
    /** Crop exactly the green-frame area. With CameraX ViewPort, normalized coordinates match PreviewView. */
    private Bitmap cropToOverlay(Bitmap frame,boolean viewportMapped){
        int vw=preview.getWidth(),vh=preview.getHeight();
        if(vw<=0||vh<=0)return null;
        int w=frame.getWidth(),h=frame.getHeight();
        float left,top,regionW,regionH;
        if(viewportMapped){
            regionW=w*widthFrac;
            regionH=h*heightFrac;
            left=(w-regionW)/2f;
            top=Math.max(0,Math.min(h-regionH,h*centerYFrac-regionH/2f));
        }else{
            float scale=Math.max(vw/(float)w,vh/(float)h);
            float visibleW=vw/scale,visibleH=vh/scale;
            float offsetX=(w-visibleW)/2f,offsetY=(h-visibleH)/2f;
            float rw=vw*widthFrac,rh=vh*heightFrac;
            left=offsetX+(vw-rw)/2f/scale;
            top=offsetY+Math.max(0,Math.min(vh-rh,vh*centerYFrac-rh/2f))/scale;
            regionW=rw/scale;regionH=rh/scale;
        }
        int x=Math.max(0,Math.min(w-1,Math.round(left)));
        int y=Math.max(0,Math.min(h-1,Math.round(top)));
        int cw=Math.min(w-x,Math.max(1,Math.round(regionW)));
        int ch=Math.min(h-y,Math.max(1,Math.round(regionH)));
        return Bitmap.createBitmap(frame,x,y,cw,ch);
    }
    /** Bundled Russian model is copied to app-private storage ONCE; no network use on the phone. */
    private void ensureRussianOcr() throws IOException {
        if (russianOcr != null) return;
        File base = new File(getFilesDir(), "subtitlevoice_ocr");
        File tessdata = new File(base, "tessdata");
        if (!tessdata.exists() && !tessdata.mkdirs())
            throw new IOException("Не удалось создать папку русской OCR-модели");
        File model = new File(tessdata, "rus.traineddata");
        if (!model.isFile() || model.length() < 1000000) {
            // Intentionally no download here: the model must be included in APK at build time.
            try (InputStream input = getAssets().open("tessdata/rus.traineddata");
                 FileOutputStream output = new FileOutputStream(model)) {
                byte[] buf = new byte[32768];
                int count;
                while ((count=input.read(buf)) != -1) output.write(buf,0,count);
            }
        }
        if (model.length() < 1000000) throw new IOException("Неполный файл rus.traineddata");
        TessBaseAPI engine = new TessBaseAPI();
        if (!engine.init(base.getAbsolutePath(), "rus", TessBaseAPI.OEM_LSTM_ONLY)) {
            engine.recycle();
            throw new IOException("Tesseract не запустил русскую модель");
        }
        engine.setPageSegMode(TessBaseAPI.PageSegMode.PSM_SINGLE_BLOCK);
        russianOcr=engine;
    }

    /** Russian text with optional line above / prefix containing the speaker name. */
    private SubtitleData extractRussianSubtitle(String raw){
        if(raw==null || raw.trim().isEmpty()) return new SubtitleData("", "");
        String speaker="";
        ArrayList<String> captions=new ArrayList<>();
        String[] lines=raw.replace('\r','\n').split("\n");
        Pattern label=Pattern.compile("(?iu)^([\\p{L}][\\p{L}\\p{M}’'\\-]{1,28})\\s*[:：—–-]\\s*(.+)$");
        for(String line:lines){
            String v=line.replaceAll("\\s+", " ").trim();
            if(v.isEmpty())continue;
            Matcher m=label.matcher(v);
            if(m.matches()){
                // Speakers are never read aloud; unknown names use the default male voice.
                speaker=resolveProfileSpeaker(m.group(1));
                v=m.group(2).trim();
            } else if(lines.length>1 && (v.endsWith(":") || v.endsWith("："))){
                String potential=v.substring(0,v.length()-1).trim();
                if(potential.matches("[\\p{L}\\p{M}’'\\-]{2,28}")) {
                    speaker=resolveProfileSpeaker(potential);
                    continue;
                }
            } else if(lines.length>1 && (isName(normalizedLabel(v)) || isRussianProfileName(v))){
                speaker=resolveProfileSpeaker(v);
                continue;
            }
            if(!v.isEmpty()) captions.add(v);
        }
        return new SubtitleData(String.join(" ",captions),speaker);
    }

    private boolean isRussianProfileName(String candidate) {
        LinkedHashMap<String,CharacterInfo> characters=profiles.get(activeGame);
        if(characters==null)return false;
        for(CharacterInfo character:characters.values())
            if(normalizedLabel(character.ru).equals(normalizedLabel(candidate))) return true;
        return false;
    }

    private String resolveProfileSpeaker(String name) {
        String normalized=normalizedLabel(name);
        LinkedHashMap<String,CharacterInfo> characters=profiles.get(activeGame);
        if(characters!=null) for(Map.Entry<String,CharacterInfo> character: characters.entrySet()) {
            if(normalizedLabel(character.getKey()).equals(normalized)
                || normalizedLabel(character.getValue().ru).equals(normalized))
                return normalizedLabel(character.getKey());
        }
        return normalized;
    }

    private static int textLength(String value){return value==null?0:value.trim().length();}

    private Bitmap enlargeSmallRussianCaption(Bitmap source){
        int w=source.getWidth(),h=source.getHeight();
        // Limit work on slow phones. Scaling cannot recover detail lost by the camera;
        // use the optical/digital camera zoom slider to get more real glyph pixels.
        float scale=Math.min(3f,Math.max(1f,340f/Math.max(1,h)));
        scale=Math.min(scale,Math.min(2800f/Math.max(1,w),850f/Math.max(1,h)));
        if(scale<=1.08f)return source;
        return Bitmap.createScaledBitmap(source,
            Math.max(1,Math.round(w*scale)),Math.max(1,Math.round(h*scale)),true);
    }

    /** Never route Cyrillic captions to ML Kit's Latin OCR. Keep Tesseract off the UI thread. */
    private void recognizeRussianFrame(Bitmap crop, long modeGeneration) {
        final int filter = contrastMode;
        russianOcrExecutor.execute(() -> {
            Bitmap prepared = null;
            try {
                ensureRussianOcr();
                // Resize based on the small OCR strip, not the size of the entire camera preview.
                // It helps Tesseract interpret narrow glyph strokes when the phone is far away.
                if(filter == 0) {
                    prepared = enlargeSmallRussianCaption(crop);
                } else {
                    prepared = enhanceSubtitleText(crop,filter==1);
                }
                russianOcr.setImage(prepared);
                String text=russianOcr.getUTF8Text();
                // Only spend time on a second OCR attempt when the first pass found nothing useful.
                if(filter==0 && (text==null || text.trim().length()<3)) {
                    Bitmap fallback=null;
                    try {
                        fallback=enhanceSubtitleText(crop,true);
                        russianOcr.setImage(fallback);
                        String second=russianOcr.getUTF8Text();
                        if(second!=null && second.trim().length()>textLength(text))text=second;
                    } finally {if(fallback!=null)fallback.recycle();}
                }
                final String recognizedText=text;
                handler.post(() -> {
                    if(!isFinishing() && !isDestroyed() && started &&
                        !translateSwitch.isChecked() && ocrModeGeneration==modeGeneration) {
                        SubtitleData data=extractRussianSubtitle(recognizedText);
                        if(data.speech.isEmpty())recognized.setText("OCR RU: текст в рамке не найден");
                        onRecognition(data); // translateOrRead() will return the original text.
                    }
                    busy=false;
                });
            } catch(Throwable error) {
                String message=error.getMessage()==null?error.getClass().getSimpleName():error.getMessage();
                handler.post(() -> {
                    if(!isFinishing() && !isDestroyed())
                        recognized.setText("Ошибка русского OCR: "+message);
                    busy=false;
                });
            } finally {
                if(prepared!=null && prepared!=crop)prepared.recycle();
                crop.recycle();
            }
        });
    }

    private void recognizeFrame(Bitmap crop){
        if(!started){crop.recycle();busy=false;return;}
        // THE LANGUAGE SWITCH IS THE ONLY INPUT-LANGUAGE SELECTOR:
        // OFF => Russian OCR, no translation. ON => English OCR + Russian translation.
        if(!translateSwitch.isChecked()) {
            recognizeRussianFrame(crop, ocrModeGeneration);
            return;
        }
        // First use the real high-resolution image: thresholding can destroy thin letters.
        recognizer.process(InputImage.fromBitmap(crop,0))
            .addOnSuccessListener(result -> {
                SubtitleData data=extractSubtitle(result);
                if(!data.speech.isEmpty() || contrastMode==0) {
                    if(data.speech.isEmpty()) recognized.setText("OCR: текст в рамке не найден");
                    onRecognition(data);crop.recycle();busy=false;
                }else recognizeEnhanced(crop);
            })
            .addOnFailureListener(e->{ show("Ошибка OCR: "+e.getMessage());crop.recycle();busy=false; });
    }
    private void recognizeEnhanced(Bitmap crop){
        final Bitmap enhanced;
        try{enhanced=enhanceSubtitleText(crop,contrastMode==1);}
        catch(Exception e){crop.recycle();busy=false;show("Ошибка контраста: "+e.getMessage());return;}
        recognizer.process(InputImage.fromBitmap(enhanced,0))
            .addOnSuccessListener(result->onRecognition(extractSubtitle(result)))
            .addOnFailureListener(e->show("Ошибка OCR: "+e.getMessage()))
            .addOnCompleteListener(task->{enhanced.recycle();crop.recycle();busy=false;});
    }
    /** Preserve OCR line boundaries: a speaker label need not contain a colon. */
    private static class SubtitleData {
        final String speech, speaker;
        SubtitleData(String speech, String speaker) {
            this.speech=speech.trim(); this.speaker=speaker == null ? "" : speaker;
        }
    }
    private static class OcrLine {
        String value;
        final Rect rect;
        final com.google.mlkit.vision.text.Text.Line source;
        OcrLine(com.google.mlkit.vision.text.Text.Line line) {
            this.source=line; this.value=line.getText().trim(); this.rect=line.getBoundingBox();
        }
    }
    private String normalizedLabel(String s) {
        return s.toLowerCase(Locale.ROOT)
            .replaceAll("^[\\s\\[({\\-–—]+", "")
            .replaceAll("[\\s\\])}:：\\-–—]+$", "").trim();
    }
    private boolean isName(String s) { return characterGender.containsKey(normalizedLabel(s)); }
    private String joinWords(List<OcrLine> lines) {
        StringBuilder b=new StringBuilder();
        for(OcrLine line:lines){ if(!line.value.isEmpty()) {if(b.length()>0)b.append(' '); b.append(line.value);} }
        return b.toString();
    }
    private SubtitleData extractSubtitle(com.google.mlkit.vision.text.Text result) {
        List<OcrLine> lines=new ArrayList<>();
        for(com.google.mlkit.vision.text.Text.TextBlock block:result.getTextBlocks())
            for(com.google.mlkit.vision.text.Text.Line line:block.getLines())
                if (!line.getText().trim().isEmpty()) lines.add(new OcrLine(line));
        // Normally subtitle labels are above their speech or at its left edge.
        lines.sort((a,b) -> {
            if(a.rect==null || b.rect==null)return 0;
            int h=Math.max(8,Math.min(a.rect.height(),b.rect.height()));
            if(Math.abs(a.rect.centerY()-b.rect.centerY()) < h*.55f)
                return Integer.compare(a.rect.left,b.rect.left);
            return Integer.compare(a.rect.top,b.rect.top);
        });
        String speaker="";
        List<OcrLine> payload=new ArrayList<>();
        for(int i=0;i<lines.size();i++) {
            OcrLine line=lines.get(i);
            String lineText=line.value;
            String solo=normalizedLabel(lineText);
            // Standalone label, including [Masha], (Masha), Masha —.
            if(isName(solo) && (lines.size()>1 || i==0)) { speaker=solo; continue; }
            // Explicitly separated label: Masha: speech; Masha — speech; [Masha] speech.
            boolean handled=false;
            for(String name:characterGender.keySet()) {
                String quoted=Pattern.quote(name);
                Pattern explicit=Pattern.compile("(?iu)^\\s*(?:\\[|\\()?"+quoted+"(?:\\]|\\))?\\s*[:：—–-]\\s*(.+)$");
                Matcher match=explicit.matcher(lineText);
                if(match.matches()) {
                    speaker=name;
                    String rest=match.group(1).trim();
                    if(!rest.isEmpty())payload.add(new OcrLineAdapter(rest,line));
                    handled=true;break;
                }
                // No punctuation: require OCR to see the name as a separate element
                // with a visibly larger-than-normal gap before the first spoken word.
                List<? extends com.google.mlkit.vision.text.Text.Element> els=line.source.getElements();
                if(els.size()>1 && normalizedLabel(els.get(0).getText()).equals(name)) {
                    Rect first=els.get(0).getBoundingBox(), second=els.get(1).getBoundingBox();
                    if(first!=null && second!=null &&
                       second.left-first.right > Math.max(8,first.height()*.6f)) {
                        speaker=name;
                        String rest=lineText.substring(Math.min(lineText.length(),els.get(0).getText().length())).trim();
                        if(!rest.isEmpty())payload.add(new OcrLineAdapter(rest,line));
                        handled=true;break;
                    }
                }
            }
            if(!handled)payload.add(line);
        }
        return new SubtitleData(joinWords(payload),speaker);
    }
    private static class OcrLineAdapter extends OcrLine {
        OcrLineAdapter(String text,OcrLine original) {super(original.source);value=text;}
    }

    /** Local adaptive threshold: separates bright/dark letter strokes from changing game scenery.
     *  The integral image makes local background estimation linear in pixel count.
     */
    private Bitmap enhanceSubtitleText(Bitmap source, boolean lightLetters) {
        int w=source.getWidth(), h=source.getHeight();
        int[] pixels=new int[w*h];
        source.getPixels(pixels,0,w,0,0,w,h);
        int[] gray=new int[w*h];
        long[] sum=new long[(w+1)*(h+1)];
        for(int y=0; y<h; y++) {
            long rowSum=0;
            for(int x=0; x<w; x++) {
                int c=pixels[y*w+x];
                int lum=(Color.red(c)*77 + Color.green(c)*150 + Color.blue(c)*29)>>8;
                gray[y*w+x]=lum;
                rowSum+=lum;
                sum[(y+1)*(w+1)+x+1]=sum[y*(w+1)+x+1]+rowSum;
            }
        }
        int[] output=new int[w*h];
        int radius=Math.max(6,Math.min(22,w/55));
        int contrast=18;
        for(int y=0;y<h;y++){
            int y0=Math.max(0,y-radius),y1=Math.min(h-1,y+radius);
            for(int x=0;x<w;x++){
                int x0=Math.max(0,x-radius),x1=Math.min(w-1,x+radius);
                long local=sum[(y1+1)*(w+1)+x1+1]-sum[y0*(w+1)+x1+1]
                          -sum[(y1+1)*(w+1)+x0]+sum[y0*(w+1)+x0];
                int mean=(int)(local/((x1-x0+1)*(y1-y0+1)));
                int lum=gray[y*w+x];
                // Dark glyphs on white are the preferred polarity for Latin OCR.
                boolean isGlyph=lightLetters ? lum>mean+contrast : lum<mean-contrast;
                output[y*w+x]=isGlyph?Color.BLACK:Color.WHITE;
            }
        }
        Bitmap bin=Bitmap.createBitmap(w,h,Bitmap.Config.ARGB_8888);
        bin.setPixels(output,0,w,0,0,w,h);
        // Upscale small captions so OCR gets wider glyph strokes.
        if (w<1100) {
            Bitmap scaled=Bitmap.createScaledBitmap(bin,w*2,h*2,false);
            bin.recycle();
            return scaled;
        }
        return bin;
    }

    /** A stable normalized representation of OCR results; punctuation and spacing are noisy. */
    private static String normalizeSpeech(String s) {
        return s.toLowerCase(Locale.ROOT)
            .replaceAll("[^\\p{L}\\p{N}]+", " ")
            .replaceAll("\\s+", " ").trim();
    }

    private static int editDistance(String a, String b) {
        int[] prev = new int[b.length()+1], next = new int[b.length()+1];
        for (int j=0; j<=b.length(); j++) prev[j]=j;
        for (int i=1; i<=a.length(); i++) {
            next[0]=i;
            for (int j=1; j<=b.length(); j++) {
                int cost=a.charAt(i-1)==b.charAt(j-1) ? 0 : 1;
                next[j]=Math.min(Math.min(next[j-1]+1, prev[j]+1),prev[j-1]+cost);
            }
            int[] tmp=prev;prev=next;next=tmp;
        }
        return prev[b.length()];
    }

    /** Suppress camera jitter and normal OCR variation, but not genuinely different lines. */
    private static boolean sameSubtitle(String first, String second) {
        String a=normalizeSpeech(first), b=normalizeSpeech(second);
        if(a.equals(b)) return true;
        if(a.isEmpty()||b.isEmpty()) return false;
        int max=Math.max(a.length(),b.length());
        int min=Math.min(a.length(),b.length());
        if(min < max * .80f) return false;
        int distance=editDistance(a,b);
        return distance<=2 || distance/(float)max <= SAME_TEXT_THRESHOLD;
    }

    private static class SpokenRecord {
        final String value;
        final long at;
        SpokenRecord(String value, long at){this.value=value;this.at=at;}
    }

    private boolean recentlyRead(String text, long now) {
        while(!recentSpeech.isEmpty() && now-recentSpeech.peekFirst().at>12000)
            recentSpeech.removeFirst();
        // A continuous subtitle should never replay just because OCR flickers.
        if(!subtitleCleared && sameSubtitle(text,lastSpoken))return true;
        // Brief disappearances caused by motion/defocus should not replay a line.
        for(SpokenRecord record:recentSpeech)
            if(now-record.at<3500 && sameSubtitle(text,record.value)) return true;
        return false;
    }

    private void onRecognition(SubtitleData data){
        if (!started) return;
        final long now=System.currentTimeMillis();
        String cleaned=data.speech.replaceAll("\\s+"," ").trim();
        if(!data.speaker.isEmpty()){
            activeSpeaker=data.speaker;
            activeSpeakerUntil=now+2500;
        }
        if(cleaned.length()<2){
            framesSinceText++;
            candidate="";attempts=0;
            // Do not clear the last spoken line after only a couple bad OCR frames.
            if(framesSinceText>=5 && now-lastTextSeenAt>700) subtitleCleared=true;
            if(framesSinceText==1)recognized.setText("OCR: субтитры не найдены (ожидание)");
            return;
        }
        lastTextSeenAt=now;
        framesSinceText=0;
        String speaker=!data.speaker.isEmpty()?data.speaker:
            now<activeSpeakerUntil?activeSpeaker:null;
        recognized.setText("OCR: "+cleaned+(speaker==null?"":"  ["+speaker+"]"));
        if(recentlyRead(cleaned,now)){
            candidate="";attempts=0;
            return;
        }
        if(!candidate.isEmpty() && sameSubtitle(candidate,cleaned)){
            attempts++;
        } else {
            candidate=cleaned;
            candidateSpeaker=speaker==null?"":speaker;
            attempts=1;
            candidateStartedAt=now;
        }
        // Confirm a significant change on 2 frames; avoids one-frame OCR hallucinations.
        // If frames are slow, accept after 300 ms to avoid waiting excessively.
        if(attempts<2 && now-candidateStartedAt<300) return;
        if(now-lastSpokenAt<300)return;
        lastSpoken=cleaned;
        lastSpokenAt=now;
        subtitleCleared=false;
        recentSpeech.addLast(new SpokenRecord(cleaned,now));
        while(recentSpeech.size()>12)recentSpeech.removeFirst();
        candidate="";attempts=0;
        final boolean male=speaker==null || characterGender.get(speaker)==null || Boolean.TRUE.equals(characterGender.get(speaker));
        final String fingerprint=cleaned;
        final long generation=translationGeneration;
        translateOrRead(cleaned, translated->{
            if(started && generation==translationGeneration && fingerprint.equals(lastSpoken)){
                recognized.setText("Озвучка: "+translated);
                speak(translated,male);
            }
        }, error->show("Ошибка перевода: "+error));
    }
    private void speak(String phrase, boolean male){
        if(!ttsReady || tts==null || phrase==null || phrase.trim().isEmpty())return;
        if(russianVoices.isEmpty()){
            show("Нет локальной русской голосовой модели в выбранном TTS-движке");
            return;
        }
        int index=male?maleIndex:femaleIndex;
        // Gender is chosen from the game profile. Unassigned characters always use male.
        if(index<1 || index>russianVoices.size())index=1;
        Voice voice=russianVoices.get(index-1);
        if(tts.setVoice(voice)==TextToSpeech.ERROR){
            show("Движок не смог включить голос: "+voice.getName());
            return;
        }
        tts.setSpeechRate(speechRate);
        tts.speak(phrase,TextToSpeech.QUEUE_FLUSH,null,"subtitle-"+System.nanoTime());
    }
    private class RoiOverlay extends View{
        private final Paint stroke=new Paint(3);
        RoiOverlay(){super(MainActivity.this);stroke.setColor(0xff55edb0);stroke.setStyle(Paint.Style.STROKE);stroke.setStrokeWidth(dp(2));}
        @Override protected void onDraw(@NonNull Canvas canvas){super.onDraw(canvas);
            float w=getWidth(),h=getHeight(), rw=w*widthFrac,rh=h*heightFrac;
            float l=(w-rw)/2, t=Math.max(0,Math.min(h-rh,h*centerYFrac-rh/2));
            canvas.drawRoundRect(new RectF(l,t,l+rw,t+rh),dp(6),dp(6),stroke);
        }
    }
    @Override protected void onDestroy(){
        translationExecutor.shutdownNow();
        handler.removeCallbacksAndMessages(null);started=false;
        recognizer.close();cameraExecutor.shutdown();if(translator!=null)translator.close();
        russianOcrExecutor.execute(() -> {if(russianOcr!=null){russianOcr.recycle();russianOcr=null;}});
        russianOcrExecutor.shutdown();
        ++ttsInitGeneration;
        if(tts!=null){tts.stop();tts.shutdown();tts=null;}
        super.onDestroy();}
}
