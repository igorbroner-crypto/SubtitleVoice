package kz.subtitlevoice;

import android.Manifest;
import android.app.AlertDialog;
import android.widget.CheckBox;
import android.widget.ProgressBar;
import java.net.URLEncoder;
import java.io.ByteArrayOutputStream;
import android.content.pm.PackageManager;
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
import android.speech.RecognizerIntent;
import android.speech.RecognitionListener;
import android.speech.SpeechRecognizer;
import android.content.Intent;
import android.os.Build;
import android.speech.tts.UtteranceProgressListener;
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
import androidx.camera.core.ImageAnalysis;
import androidx.camera.core.ImageProxy;
import androidx.camera.core.Preview;
import androidx.camera.lifecycle.ProcessCameraProvider;
import androidx.camera.view.PreviewView;
import androidx.core.content.ContextCompat;

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
import org.json.JSONArray;
import org.json.JSONObject;
import java.net.HttpURLConnection;
import java.net.URL;
import java.io.OutputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import android.text.InputType;
import java.util.regex.*;

/** Camera->cropped OCR->optional offline translation->speech. No screenshot storage. */
public class MainActivity extends AppCompatActivity {
    private final Handler handler = new Handler(Looper.getMainLooper());
    private final ExecutorService cameraExecutor = Executors.newSingleThreadExecutor();
    private final TextRecognizer recognizer = TextRecognition.getClient(TextRecognizerOptions.DEFAULT_OPTIONS);
    private final Map<String, Boolean> characterGender = new LinkedHashMap<>();
    private final ArrayList<Voice> russianVoices = new ArrayList<>();
    private SharedPreferences prefs;
    private final LinkedHashMap<String, LinkedHashMap<String, CharacterInfo>> profiles = new LinkedHashMap<>();
    private String activeGame = "Без игры";
    private Spinner gameSpinner, translationModeSpinner;
    private EditText apiKeyInput;
    private boolean updatingGames = false;
    private final ExecutorService translationExecutor = Executors.newSingleThreadExecutor();
    private final Deque<String> dialogueHistory = new ArrayDeque<>();
    private long translationGeneration = 0;
    private int translationMode = 0;
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
    private boolean audioMode = false, microphoneActive = false, audioPending = false, audioTtsPlaying = false;
    private SpeechRecognizer speechRecognizer;
    private LinearLayout cameraPanel, audioPanel;
    private TextView audioStatus, audioTranscript;
    private Spinner modeSpinner, audioGenderSpinner;
    // Estimate pitch only when the installed Android recognizer provides PCM buffers.
    private int pitchMaleVotes = 0, pitchFemaleVotes = 0;
    private String lastAudioText = "";
    private long lastAudioAt = 0;
    private final Runnable retryMicrophone = () -> beginListening();
    private final ActivityResultLauncher<String> microphonePermission = registerForActivityResult(
        new ActivityResultContracts.RequestPermission(), granted -> {
            if (granted && audioMode) startMicrophone();
            else if (!granted && audioMode) show("Разреши доступ к микрофону");
        });
    private PreviewView preview;
    private RoiOverlay overlay;
    private TextView status, recognized, speedLabel, namesLabel;
    private ImageView ocrPreview;
    private Switch showOcrPreviewSwitch;
    private Spinner maleSpinner, femaleSpinner, defaultSpinner;
    private Switch translateSwitch;
    private TextToSpeech tts;
    private Translator translator;
    private boolean translatorReady = false, ttsReady = false, started = false, busy = false;
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
    private int maleIndex = 0, femaleIndex = 0, defaultKind = 0, contrastMode = 0;
    private static final float SAME_TEXT_THRESHOLD = .12f;
    private final ActivityResultLauncher<String> cameraPermission = registerForActivityResult(new ActivityResultContracts.RequestPermission(), allowed -> {
        if (allowed) startCamera(); else show("Нужно разрешение камеры");
    });

    @Override public void onCreate(Bundle state) {
        super.onCreate(state);
        prefs = getSharedPreferences("subtitle_voice", MODE_PRIVATE);
        widthFrac = prefs.getFloat("roiWidth", .82f);
        heightFrac = prefs.getFloat("roiHeight", .17f);
        centerYFrac = prefs.getFloat("roiCenter", .80f);
        speechRate = prefs.getFloat("speechRate", 1.25f);
        maleIndex = prefs.getInt("maleVoice", 0);
        femaleIndex = prefs.getInt("femaleVoice", 0);
        defaultKind = prefs.getInt("defaultKind", 0);
        contrastMode = prefs.getInt("contrastMode", 0);
        audioMode = prefs.getInt("mode", 0) == 1;
        loadProfiles();
        translationMode = 0;
        activeGame = prefs.getString("activeGameV16", "Без игры");
        if (!profiles.containsKey(activeGame)) activeGame="Без игры";
        activateGame(activeGame);
        buildUi();
        tts = new TextToSpeech(this, code -> handler.post(() -> {
            ttsReady = code == TextToSpeech.SUCCESS;
            if (ttsReady) {
                tts.setLanguage(new Locale("ru", "RU")); populateVoices();
                tts.setOnUtteranceProgressListener(new UtteranceProgressListener() {
                    @Override public void onStart(String id) {}
                    @Override public void onDone(String id) { handler.post(() -> onAudioSpeechFinished()); }
                    @Override public void onError(String id) { handler.post(() -> onAudioSpeechFinished()); }
                });
            }
            else show("Не найден движок озвучки Android");
        }));
        TranslatorOptions options = new TranslatorOptions.Builder()
            .setSourceLanguage(TranslateLanguage.ENGLISH).setTargetLanguage(TranslateLanguage.RUSSIAN).build();
        translator = Translation.getClient(options);
        if (translateSwitch.isChecked()) prepareTranslator();
        if (audioMode) requestMicrophone();
        else requestCamera();
    }

    private int dp(float value) { return (int)(getResources().getDisplayMetrics().density * value + .5f); }
    private TextView text(String s, int sp) { TextView t = new TextView(this); t.setText(s); t.setTextColor(Color.WHITE); t.setTextSize(sp); t.setPadding(dp(4),dp(6),dp(4),dp(6)); return t; }
    private LinearLayout.LayoutParams full() { return new LinearLayout.LayoutParams(-1, -2); }
    private void add(LinearLayout l, View v) { l.addView(v,full()); }
    private void buildUi() {
        LinearLayout root = new LinearLayout(this); root.setOrientation(LinearLayout.VERTICAL); root.setBackgroundColor(Color.rgb(13,18,29));
        ScrollView scroll = new ScrollView(this); root.addView(scroll);
        LinearLayout content = new LinearLayout(this); content.setOrientation(LinearLayout.VERTICAL); content.setPadding(dp(12), dp(10), dp(12), dp(18)); scroll.addView(content);
        add(content, text("SUBTITLE VOICE   •   Перевод и озвучка", 19));
        add(content, text("Режим работы", 16));
        modeSpinner = new Spinner(this);
        modeSpinner.setAdapter(new ArrayAdapter<>(this, android.R.layout.simple_spinner_dropdown_item,
            new String[]{"Озвучка по субтитрам", "Озвучка по аудио"}));
        modeSpinner.setSelection(audioMode ? 1 : 0);
        add(content, modeSpinner);
        cameraPanel = new LinearLayout(this);
        cameraPanel.setOrientation(LinearLayout.VERTICAL);
        add(content, cameraPanel);
        audioPanel = new LinearLayout(this);
        audioPanel.setOrientation(LinearLayout.VERTICAL);
        add(content, audioPanel);
        add(audioPanel, text("Режим микрофона: английская речь с телевизора → перевод на русский → голос", 13));
        audioStatus = text("Микрофон не запущен", 13); add(audioPanel, audioStatus);
        audioTranscript = text("Распознано: —", 14); add(audioPanel, audioTranscript);
        add(audioPanel, text("Пол голоса определяется приблизительно по высоте тона, только если речевой движок предоставляет аудиобуфер. Если данных нет, используется выбор ниже.", 12));
        audioGenderSpinner = new Spinner(this);
        audioGenderSpinner.setAdapter(new ArrayAdapter<>(this, android.R.layout.simple_spinner_dropdown_item,
            new String[]{"Авто (экспериментально)", "Всегда мужской", "Всегда женский"}));
        audioGenderSpinner.setSelection(prefs.getInt("audioGenderMode", 0));
        add(audioPanel, audioGenderSpinner);
        audioGenderSpinner.setOnItemSelectedListener(new SpinnerListener(i ->
            prefs.edit().putInt("audioGenderMode", i).apply()));
        Button audioToggle = new Button(this);
        audioToggle.setText("Остановить / запустить прослушивание");
        add(audioPanel, audioToggle);
        audioToggle.setOnClickListener(v -> {
            if (microphoneActive) stopMicrophone(); else requestMicrophone();
        });
        add(audioPanel, text("Чтобы микрофон не распознавал синтезированную речь повторно, прослушивание приостанавливается на время озвучки. Лучше пользоваться наушниками.", 12));
        cameraPanel.setVisibility(audioMode ? View.GONE : View.VISIBLE);
        audioPanel.setVisibility(audioMode ? View.VISIBLE : View.GONE);
        modeSpinner.setOnItemSelectedListener(new SpinnerListener(i -> switchMode(i == 1)));
        FrameLayout stage = new FrameLayout(this);
        stage.setBackgroundColor(Color.BLACK);
        add(cameraPanel, stage);
        stage.getLayoutParams().height = dp(300);
        preview = new PreviewView(this);
        preview.setScaleType(PreviewView.ScaleType.FILL_CENTER);
        stage.addView(preview, new FrameLayout.LayoutParams(-1,-1));
        overlay = new RoiOverlay(); stage.addView(overlay,new FrameLayout.LayoutParams(-1,-1));
        add(cameraPanel, text("Распознаётся ТОЛЬКО область внутри рамки. Наведи камеру на центр нижней части ТВ.", 12));
        status = text("Инициализация…", 13); add(cameraPanel,status);
        recognized = text("Последняя реплика: —", 14); add(cameraPanel,recognized);
        showOcrPreviewSwitch = new Switch(this);
        showOcrPreviewSwitch.setText("Показывать реальный кадр OCR (для настройки рамки)");
        showOcrPreviewSwitch.setTextColor(Color.WHITE);
        showOcrPreviewSwitch.setChecked(prefs.getBoolean("debugCrop", true));
        add(cameraPanel, showOcrPreviewSwitch);
        showOcrPreviewSwitch.setOnCheckedChangeListener((b, enabled) -> {
            prefs.edit().putBoolean("debugCrop", enabled).apply();
            ocrPreview.setVisibility(enabled ? View.VISIBLE : View.GONE);
        });
        ocrPreview = new ImageView(this);
        ocrPreview.setAdjustViewBounds(true);
        ocrPreview.setScaleType(ImageView.ScaleType.FIT_CENTER);
        ocrPreview.setBackgroundColor(Color.rgb(28, 31, 40));
        ocrPreview.setMaxHeight(dp(130));
        ocrPreview.setVisibility(showOcrPreviewSwitch.isChecked() ? View.VISIBLE : View.GONE);
        add(cameraPanel, ocrPreview);
        add(cameraPanel, text("Проверка OCR: здесь должны быть видны ВСЕ буквы субтитра, без верхних меню игры.", 12));
        Button toggle = new Button(this); toggle.setText("Пауза распознавания"); add(cameraPanel,toggle);
        toggle.setOnClickListener(v -> { started = !started; toggle.setText(started ? "Пауза распознавания" : "Продолжить распознавание"); if (!started && tts != null) tts.stop(); });
        add(cameraPanel,text("Область субтитров",16));
        add(cameraPanel,text("Контраст субтитров на фоне игры",16));
        add(cameraPanel,text("Если у субтитров нет чёрной подложки, попробуй режим «Светлые буквы». Он выделяет текст относительно окружающего фона.",12));
        Spinner contrastSpinner = new Spinner(this);
        contrastSpinner.setAdapter(new ArrayAdapter<>(this, android.R.layout.simple_spinner_dropdown_item,
            new String[]{"HD без фильтра (рекомендуется)", "Светлые буквы на пёстром фоне", "Тёмные буквы на пёстром фоне"}));
        contrastSpinner.setSelection(contrastMode);
        contrastSpinner.setOnItemSelectedListener(new SpinnerListener(i -> {
            contrastMode=i; prefs.edit().putInt("contrastMode",i).apply();
        }));
        add(cameraPanel,contrastSpinner);
        addSlider(content,"Ширина рамки",55,100,Math.round(widthFrac*100), value -> {widthFrac=value/100f; saveRoi();});
        addSlider(content,"Высота рамки",7,35,Math.round(heightFrac*100), value -> {heightFrac=value/100f; saveRoi();});
        addSlider(content,"Положение по вертикали",55,95,Math.round(centerYFrac*100), value -> {centerYFrac=value/100f;saveRoi();});
        speedLabel = text("Скорость речи: " + String.format(Locale.US,"%.2f×",speechRate),16); add(content,speedLabel);
        SeekBar speechSlider = new SeekBar(this); speechSlider.setMax(130); speechSlider.setProgress(Math.round((speechRate-.7f)*100)); add(content,speechSlider);
        speechSlider.setOnSeekBarChangeListener(new SimpleSeekListener(v -> {
            speechRate = .7f + v / 100f; speedLabel.setText("Скорость речи: " + String.format(Locale.US,"%.2f×",speechRate));
            prefs.edit().putFloat("speechRate",speechRate).apply();
            if (ttsReady) tts.setSpeechRate(speechRate);
        }));
        translateSwitch = new Switch(this); translateSwitch.setText("Переводить английские субтитры на русский"); translateSwitch.setTextColor(Color.WHITE);
        translateSwitch.setChecked(prefs.getBoolean("translate",true)); add(content,translateSwitch);
        translateSwitch.setOnCheckedChangeListener((button, enabled) -> { prefs.edit().putBoolean("translate",enabled).apply(); if (enabled) prepareTranslator(); });
        add(content,text("Перевод: офлайн ML Kit. Интернет используется только при ручном импорте списка персонажей; платные API не нужны.",12));
        add(content,text("Голоса персонажей (доступные русские голоса телефона)",16));
        add(content,text("Для мужского и женского голоса выбери разные варианты и проверь их кнопками. Android не сообщает пол голоса автоматически.",12));
        add(content,text("Мужской голос",13)); maleSpinner = new Spinner(this);add(content,maleSpinner);
        Button testM = new Button(this);testM.setText("Проверить мужской");add(content,testM);testM.setOnClickListener(v->speak("Привет! Это пример мужского голоса.",true));
        add(content,text("Женский голос",13)); femaleSpinner = new Spinner(this);add(content,femaleSpinner);
        Button testF = new Button(this);testF.setText("Проверить женский");add(content,testF);testF.setOnClickListener(v->speak("Привет! Это пример женского голоса.",false));
        add(content,text("Голос по умолчанию (для реплик без имени)",13));
        defaultSpinner = new Spinner(this); add(content,defaultSpinner);
        ArrayAdapter<String> defaultAdapter = new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,new String[]{"Мужской","Женский"});
        defaultSpinner.setAdapter(defaultAdapter);defaultSpinner.setSelection(defaultKind);
        defaultSpinner.setOnItemSelectedListener(new SpinnerListener(index -> {defaultKind=index;prefs.edit().putInt("defaultKind",index).apply();}));
        add(content,text("ПРОФИЛИ ИГР И ПЕРСОНАЖЕЙ",17));
        add(content,text("Для каждой игры свой список имён, произношений и голосов. Выбор профиля также меняет словарь перевода.",12));
        gameSpinner=new Spinner(this);add(content,gameSpinner);
        refreshGameSpinner();
        gameSpinner.setOnItemSelectedListener(new SpinnerListener(i->{
            if(!updatingGames && i>=0 && i<profiles.size()){
                String selected=new ArrayList<>(profiles.keySet()).get(i);
                if(!selected.equals(activeGame)){activeGame=selected;activateGame(activeGame);prefs.edit().putString("activeGameV16",activeGame).apply();translationGeneration++;dialogueHistory.clear();renderNames();}
            }
        }));
        EditText gameInput=new EditText(this);gameInput.setHint("Название игры: Final Fantasy VII");gameInput.setTextColor(Color.WHITE);gameInput.setSingleLine(true);add(content,gameInput);
        Button addGame=new Button(this);addGame.setText("Создать / выбрать игру");add(content,addGame);
        addGame.setOnClickListener(v->{
            String name=gameInput.getText().toString().trim();
            if(name.isEmpty())return;
            profiles.putIfAbsent(name,new LinkedHashMap<>());
            activeGame=name;activateGame(name);saveProfiles();refreshGameSpinner();renderNames();gameInput.setText("");dialogueHistory.clear();translationGeneration++;
        });
        Button importGame=new Button(this);
        importGame.setText("Найти персонажей игры в интернете (один раз)"); add(content,importGame);
        importGame.setOnClickListener(v->{
            String game=gameInput.getText().toString().trim();
            if(game.isEmpty())game=activeGame;
            if(game.equals("Без игры")){show("Сначала введи название игры или выбери профиль");return;}
            importCharactersFromWikidata(game,importGame);
        });
        add(content,text("Импорт необязателен: интернет используется только при нажатии этой кнопки. Во время распознавания, офлайн-перевода и озвучки список хранится на телефоне. Wikidata может содержать неполный список.",12));
        Button removeGame=new Button(this);removeGame.setText("Удалить выбранный профиль игры");add(content,removeGame);
        removeGame.setOnClickListener(v->{
            if("Без игры".equals(activeGame)){Toast.makeText(this,"Базовый профиль нельзя удалить",Toast.LENGTH_SHORT).show();return;}
            profiles.remove(activeGame);activeGame="Без игры";activateGame(activeGame);saveProfiles();refreshGameSpinner();renderNames();dialogueHistory.clear();translationGeneration++;
        });
        add(content,text("Персонажи текущей игры",16));
        namesLabel=text("",13);add(content,namesLabel);renderNames();
        EditText nameInput = new EditText(this);nameInput.setTextColor(Color.WHITE);nameInput.setHint("Имя в субтитрах: Cloud");nameInput.setSingleLine(true);add(content,nameInput);
        EditText aliasesInput = new EditText(this);aliasesInput.setTextColor(Color.WHITE);aliasesInput.setHint("Другие написания через запятую: Cloude");aliasesInput.setSingleLine(true);add(content,aliasesInput);
        EditText russianNameInput=new EditText(this);russianNameInput.setTextColor(Color.WHITE);russianNameInput.setHint("Как произносить по-русски: Клауд");russianNameInput.setSingleLine(true);add(content,russianNameInput);
        Spinner gender = new Spinner(this);gender.setAdapter(new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,new String[]{"Мужской","Женский"}));add(content,gender);
        Button addName = new Button(this);addName.setText("Добавить / изменить персонажа");add(content,addName);
        addName.setOnClickListener(v->{
            String n=nameInput.getText().toString().trim();
            String ru=russianNameInput.getText().toString().trim();
            if(n.isEmpty()||ru.isEmpty()){Toast.makeText(this,"Укажи имя и русское произношение",Toast.LENGTH_SHORT).show();return;}
            LinkedHashMap<String,CharacterInfo> list=profiles.get(activeGame);
            CharacterInfo info=new CharacterInfo(ru,gender.getSelectedItemPosition()==0);
            list.put(n,info);
            for(String alias:aliasesInput.getText().toString().split(",")) if(!alias.trim().isEmpty())list.put(alias.trim(),info);
            activateGame(activeGame);saveProfiles();renderNames();
            nameInput.setText("");aliasesInput.setText("");russianNameInput.setText("");
        });
        Button remove = new Button(this);remove.setText("Удалить имя / псевдоним из профиля");add(content,remove);
        remove.setOnClickListener(v->{
            String n=nameInput.getText().toString().trim();
            String key=null;for(String k:profiles.get(activeGame).keySet())if(k.equalsIgnoreCase(n))key=k;
            if(key!=null){CharacterInfo item=profiles.get(activeGame).get(key);profiles.get(activeGame).entrySet().removeIf(e->e.getValue()==item);activateGame(activeGame);saveProfiles();renderNames();}
        });
        add(content,text("Совет: зафиксируй телефон на подставке. Если субтитры обновляются быстро, увеличь скорость до 1.4–1.7×.",12));
        setContentView(root);
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
        JSONObject value = snak == null ? null :
    (snak.optJSONObject("datavalue") == null ? null :
    snak.optJSONObject("datavalue").optJSONObject("value"));
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
            .setPositiveButton("Сохранить в профиль",(d,w)->{
                profiles.putIfAbsent(game,new LinkedHashMap<>());
                LinkedHashMap<String,CharacterInfo> list=profiles.get(game);
                int added=0;
                for(int i=0;i<characters.size();i++){
                    if(!checks.get(i).isChecked()||genders.get(i).getSelectedItemPosition()==2)continue;
                    String ru=names.get(i).getText().toString().trim();if(ru.isEmpty())continue;
                    list.put(characters.get(i).english,new CharacterInfo(ru,genders.get(i).getSelectedItemPosition()==0));added++;
                }
                activeGame=game;saveProfiles();activateGame(game);refreshGameSpinner();renderNames();
                dialogueHistory.clear();translationGeneration++;
                show("Сохранено персонажей: "+added+". Для игры не потребуется интернет.");
            }).show();
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
    private void translateWithContext(String input, java.util.function.Consumer<String> success, java.util.function.Consumer<String> failure){
        if(translationMode==0){
            if(!translatorReady){failure.accept("Ожидаю загрузку офлайн-переводчика");return;}
            // Name normalization works offline, but ML Kit still translates one phrase at a time.
            translator.translate(protectNames(input))
                .addOnSuccessListener(r->{rememberDialogue(input,r);success.accept(r);})
                .addOnFailureListener(e->failure.accept(e.getMessage()));
            return;
        }
        String key=prefs.getString("onlineApiKeyV16","").trim();
        if(key.isEmpty()){failure.accept("Добавь OpenAI API-ключ или включи офлайн-перевод");return;}
        final String game=activeGame, glossarySnapshot=glossary();
        final ArrayList<String> history=new ArrayList<>(dialogueHistory);
        translationExecutor.execute(()->{
            HttpURLConnection conn=null;
            try{
                conn=(HttpURLConnection)new URL("https://api.openai.com/v1/chat/completions").openConnection();
                conn.setRequestMethod("POST");conn.setConnectTimeout(3500);conn.setReadTimeout(7000);
                conn.setDoOutput(true);conn.setRequestProperty("Content-Type","application/json; charset=utf-8");
                conn.setRequestProperty("Authorization","Bearer "+key);
                String rules="Translate the newest English video-game dialogue to natural spoken Russian, not word-for-word. " +
                    "Preserve meaning, emotions, pronouns and character context. Only output the translation, no commentary. " +
                    "Game: "+game+". Character name glossary (must use these exact Russian spellings): "+glossarySnapshot+
                    ". Previous dialogue lines are context ONLY; do not translate them again. Keep the new utterance concise.";
                JSONArray messages=new JSONArray();
                messages.put(new JSONObject().put("role","system").put("content",rules));
                messages.put(new JSONObject().put("role","user").put("content","Context:\n"+String.join("\n",history)+"\nNEW LINE:\n"+input));
                JSONObject request=new JSONObject().put("model","gpt-4.1-mini").put("messages",messages).put("max_tokens",240).put("temperature",0.25);
                try(OutputStream out=conn.getOutputStream()){out.write(request.toString().getBytes(StandardCharsets.UTF_8));}
                int code=conn.getResponseCode();
                InputStream in=code<300?conn.getInputStream():conn.getErrorStream();
                byte[] bytes=in.readAllBytes();String body=new String(bytes,StandardCharsets.UTF_8);
                if(code>=300)throw new Exception("API HTTP "+code+": "+body.substring(0,Math.min(body.length(),180)));
                String translated=new JSONObject(body).getJSONArray("choices").getJSONObject(0).getJSONObject("message").getString("content").trim();
                if(translated.isEmpty())throw new Exception("Пустой перевод");
                handler.post(()->{if(game.equals(activeGame)){rememberDialogue(input,translated);success.accept(translated);}});
            }catch(Exception e){handler.post(()->failure.accept(e.getMessage()==null?"Сетевая ошибка":e.getMessage()));}
            finally{if(conn!=null)conn.disconnect();}
        });
    }
    private void rememberDialogue(String source,String translation){
        dialogueHistory.addLast("EN: "+source+" | RU: "+translation);
        while(dialogueHistory.size()>8)dialogueHistory.removeFirst();
    }
    private void populateVoices(){
        russianVoices.clear();
        if(tts.getVoices()!=null)for(Voice voice:tts.getVoices())if("ru".equals(voice.getLocale().getLanguage()))russianVoices.add(voice);
        russianVoices.sort(Comparator.comparing(Voice::getName));
        List<String> titles=new ArrayList<>();titles.add("Системный русский голос");
        for(Voice voice:russianVoices)titles.add(voice.getName()+(voice.isNetworkConnectionRequired()?" (интернет)":" (офлайн)"));
        ArrayAdapter<String> adapterM=new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,titles);
        ArrayAdapter<String> adapterF=new ArrayAdapter<>(this,android.R.layout.simple_spinner_dropdown_item,titles);
        maleSpinner.setAdapter(adapterM); femaleSpinner.setAdapter(adapterF);
        maleSpinner.setSelection(Math.min(maleIndex,titles.size()-1)); femaleSpinner.setSelection(Math.min(femaleIndex,titles.size()-1));
        maleSpinner.setOnItemSelectedListener(new SpinnerListener(n->{maleIndex=n;prefs.edit().putInt("maleVoice",n).apply();}));
        femaleSpinner.setOnItemSelectedListener(new SpinnerListener(n->{femaleIndex=n;prefs.edit().putInt("femaleVoice",n).apply();}));
    }
    private void prepareTranslator(){
        if(translatorReady){show("Перевод офлайн готов");return;}
        show("Подготавливаю языковую модель перевода (первый запуск требует интернет)…");
        translator.downloadModelIfNeeded(new DownloadConditions.Builder().build())
          .addOnSuccessListener(v->{translatorReady=true;lastSpoken="";show("Перевод офлайн готов");})
          .addOnFailureListener(e->show("Не удалось скачать модель перевода: "+e.getMessage()));
    }
    private void requestCamera() {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) startCamera();
        else cameraPermission.launch(Manifest.permission.CAMERA);
    }
    private void requestMicrophone() {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED) startMicrophone();
        else microphonePermission.launch(Manifest.permission.RECORD_AUDIO);
    }
    private void switchMode(boolean useAudio) {
        if (useAudio == audioMode) return;
        translationGeneration++;
        audioMode = useAudio;
        prefs.edit().putInt("mode", audioMode ? 1 : 0).apply();
        cameraPanel.setVisibility(audioMode ? View.GONE : View.VISIBLE);
        audioPanel.setVisibility(audioMode ? View.VISIBLE : View.GONE);
        if (tts != null) tts.stop();
        audioTtsPlaying = false;
        audioPending = false;
        if (audioMode) {
            started = false;
            requestMicrophone();
        } else {
            stopMicrophone();
            requestCamera();
        }
    }
    private void startMicrophone() {
        if (!audioMode) return;
        if (!SpeechRecognizer.isRecognitionAvailable(this)) {
            audioStatus.setText("На телефоне нет доступной службы распознавания речи Android");
            return;
        }
        if (speechRecognizer == null) {
            speechRecognizer = SpeechRecognizer.createSpeechRecognizer(this);
            speechRecognizer.setRecognitionListener(new RecognitionListener() {
                @Override public void onReadyForSpeech(Bundle b) { audioStatus.setText("Слушаю английскую речь…"); }
                @Override public void onBeginningOfSpeech() { audioStatus.setText("Слышу речь…"); }
                @Override public void onRmsChanged(float rms) {}
                @Override public void onBufferReceived(byte[] bytes) { estimateVoicePitch(bytes); }
                @Override public void onEndOfSpeech() { audioStatus.setText("Распознаю…"); }
                @Override public void onError(int code) {
                    if (!microphoneActive || !audioMode) return;
                    if (code == SpeechRecognizer.ERROR_INSUFFICIENT_PERMISSIONS) {
                        audioStatus.setText("Нет разрешения на микрофон"); stopMicrophone(); return;
                    }
                    audioStatus.setText("Перезапуск прослушивания (" + code + ")…");
                    if (!audioPending && !audioTtsPlaying) scheduleMicrophone(600);
                }
                @Override public void onResults(Bundle results) {
                    if (!microphoneActive || !audioMode) return;
                    ArrayList<String> list = results.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION);
                    String phrase = list == null || list.isEmpty() ? "" : list.get(0).trim();
                    if (phrase.isEmpty()) { scheduleMicrophone(250); return; }
                    handleAudioPhrase(phrase);
                }
                @Override public void onPartialResults(Bundle results) {
                    ArrayList<String> list = results.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION);
                    if (microphoneActive && audioMode && list != null && !list.isEmpty())
                        audioTranscript.setText("Слышу: " + list.get(0));
                }
                @Override public void onEvent(int type, Bundle params) {}
            });
        }
        microphoneActive = true;
        beginListening();
    }
    private void beginListening() {
        if (!audioMode || !microphoneActive || audioPending || audioTtsPlaying || speechRecognizer == null) return;
        pitchMaleVotes = 0; pitchFemaleVotes = 0;
        Intent intent = new Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH);
        intent.putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM);
        intent.putExtra(RecognizerIntent.EXTRA_LANGUAGE, "en-US");
        intent.putExtra(RecognizerIntent.EXTRA_PARTIAL_RESULTS, true);
        intent.putExtra(RecognizerIntent.EXTRA_MAX_RESULTS, 1);
        intent.putExtra(RecognizerIntent.EXTRA_SPEECH_INPUT_COMPLETE_SILENCE_LENGTH_MILLIS, 400L);
        intent.putExtra(RecognizerIntent.EXTRA_SPEECH_INPUT_POSSIBLY_COMPLETE_SILENCE_LENGTH_MILLIS, 300L);
        try { speechRecognizer.startListening(intent); }
        catch (Exception e) { audioStatus.setText("Ошибка микрофона: " + e.getMessage()); }
    }
    private void scheduleMicrophone(long delay) {
        handler.removeCallbacks(retryMicrophone);
        if (microphoneActive && audioMode && !audioPending && !audioTtsPlaying)
            handler.postDelayed(retryMicrophone, delay);
    }
    private void stopMicrophone() {
        microphoneActive = false;
        audioPending = false;
        handler.removeCallbacks(retryMicrophone);
        if (speechRecognizer != null) speechRecognizer.cancel();
        if (audioStatus != null) audioStatus.setText("Микрофон остановлен");
    }
    /** A conservative approximation, not a biological gender classifier.
     * Android recognition services may never invoke onBufferReceived; in that case
     * the fallback voice is used. PCM16 16-kHz data is assumed only for this optional estimate.
     */
    private void estimateVoicePitch(byte[] pcm) {
        if (pcm == null || pcm.length < 1024 || pcm.length > 64000) return;
        int length = Math.min(pcm.length / 2, 4096);
        float[] samples = new float[length];
        double energy = 0;
        for (int i=0; i<length; i++) {
            int lo = pcm[2*i] & 0xff;
            short sample = (short) ((pcm[2*i+1] << 8) | lo);
            samples[i] = sample / 32768f;
            energy += samples[i] * samples[i];
        }
        if (energy / length < .001) return;
        // 16-kHz autocorrelation of voiced frames, 85–300 Hz.
        int minLag = 16000/300, maxLag = Math.min(length/2,16000/85);
        double best = 0; int peak = 0;
        for (int lag=minLag; lag<=maxLag; lag+=2) {
            double correlation=0, power=0;
            for(int j=0;j<length-lag;j+=3) {
                correlation += samples[j]*samples[j+lag];
                power += samples[j]*samples[j];
            }
            if(power>0 && correlation/power>best) {best=correlation/power;peak=lag;}
        }
        if(best<.62 || peak==0) return;
        float f0 = 16000f / peak;
        if (f0 < 155) pitchMaleVotes++;
        else if(f0 > 190) pitchFemaleVotes++;
    }
    private boolean audioMaleVoice() {
        int selected=audioGenderSpinner.getSelectedItemPosition();
        if (selected==1) return true;
        if (selected==2) return false;
        if (pitchMaleVotes + pitchFemaleVotes < 3 || Math.abs(pitchMaleVotes-pitchFemaleVotes)<2)
            return defaultKind==0;
        return pitchMaleVotes>pitchFemaleVotes;
    }
    private void handleAudioPhrase(String phrase) {
        long now = System.currentTimeMillis();
        audioTranscript.setText("Распознано: " + phrase);
        if (phrase.equalsIgnoreCase(lastAudioText) && now-lastAudioAt<4000) {
            scheduleMicrophone(250); return;
        }
        lastAudioText=phrase; lastAudioAt=now;
        final boolean male=audioMaleVoice();
        audioPending=true;
        if (!translateSwitch.isChecked()) {
            speakAudio(phrase,male); return;
        }
        final long generation=translationGeneration;
        translateWithContext(phrase,r->{
            if(generation==translationGeneration && audioMode && microphoneActive)speakAudio(r,male);
            else audioPending=false;
        },error->{
            audioPending=false;
            audioStatus.setText("Ошибка перевода: " + error);
            scheduleMicrophone(350);
        });
    }
    private void speakAudio(String text, boolean male) {
        audioPending=false;
        if (!microphoneActive || !audioMode) return;
        if (!ttsReady || text.trim().isEmpty()) { scheduleMicrophone(300); return; }
        audioTtsPlaying=true;
        audioStatus.setText("Озвучиваю: " + text);
        speak(text,male);
    }
    private void onAudioSpeechFinished() {
        if (audioTtsPlaying) {
            audioTtsPlaying=false;
            scheduleMicrophone(200);
        }
    }
    private void startCamera(){
        ListenableFuture<ProcessCameraProvider> future=ProcessCameraProvider.getInstance(this);
        future.addListener(()->{
            try{
                ProcessCameraProvider provider=future.get();provider.unbindAll();
                Preview p=new Preview.Builder().build();p.setSurfaceProvider(preview.getSurfaceProvider());
                ImageAnalysis analysis = new ImageAnalysis.Builder()
                    .setTargetResolution(new Size(1280, 720))
                    .setOutputImageFormat(ImageAnalysis.OUTPUT_IMAGE_FORMAT_RGBA_8888)
                    .setBackpressureStrategy(ImageAnalysis.STRATEGY_KEEP_ONLY_LATEST)
                    .build();
                analysis.setAnalyzer(cameraExecutor, frame -> {
                    if (audioMode || !started || busy) {frame.close();return;}
                    busy=true;
                    try {
                        Bitmap captured=bitmapFromFrame(frame);
                        int rotation=frame.getImageInfo().getRotationDegrees();
                        frame.close();
                        Bitmap oriented=captured;
                        if(rotation!=0){
                            Matrix rotate=new Matrix(); rotate.postRotate(rotation);
                            oriented=Bitmap.createBitmap(captured,0,0,captured.getWidth(),captured.getHeight(),rotate,true);
                            captured.recycle();
                        }
                        Bitmap cropped=cropToOverlay(oriented);
                        oriented.recycle();
                        if(cropped==null){busy=false;return;}
                        runOnUiThread(()->recognizeFrame(cropped));
                    }catch(Exception e){
                        frame.close(); busy=false;
                        runOnUiThread(()->show("Ошибка кадра: "+e.getMessage()));
                    }
                });
                provider.bindToLifecycle(this,CameraSelector.DEFAULT_BACK_CAMERA,p,analysis);
                started=true;show("Камера HD готова. Наведи рамку на субтитры");
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
    /** PreviewView uses FILL_CENTER; map the visible rectangle back to full-resolution frame. */
    private Bitmap cropToOverlay(Bitmap frame){
        int vw=preview.getWidth(),vh=preview.getHeight();
        if(vw<=0||vh<=0)return null;
        int w=frame.getWidth(),h=frame.getHeight();
        float scale=Math.max(vw/(float)w,vh/(float)h);
        float visibleW=vw/scale, visibleH=vh/scale;
        float offsetX=(w-visibleW)/2f,offsetY=(h-visibleH)/2f;
        float rw=vw*widthFrac,rh=vh*heightFrac;
        float leftInView=(vw-rw)/2f;
        float topInView=Math.max(0,Math.min(vh-rh,vh*centerYFrac-rh/2f));
        int left=Math.max(0,Math.min(w-1,Math.round(offsetX+leftInView/scale)));
        int top=Math.max(0,Math.min(h-1,Math.round(offsetY+topInView/scale)));
        int cropW=Math.min(w-left,Math.max(20,Math.round(rw/scale)));
        int cropH=Math.min(h-top,Math.max(20,Math.round(rh/scale)));
        return Bitmap.createBitmap(frame,left,top,cropW,cropH);
    }
    private void recognizeFrame(Bitmap crop){
        // Show the EXACT cropped bitmap passed to the OCR engine, not the camera preview.
        if (showOcrPreviewSwitch != null && showOcrPreviewSwitch.isChecked()) {
            float shrink = Math.min(1f, 800f / crop.getWidth());
            Bitmap diagnostic = Bitmap.createScaledBitmap(crop,
                Math.max(1, Math.round(crop.getWidth() * shrink)),
                Math.max(1, Math.round(crop.getHeight() * shrink)), true);
            // createScaledBitmap can return the original object when dimensions match.
            if (diagnostic == crop) diagnostic = crop.copy(Bitmap.Config.ARGB_8888, false);
            ocrPreview.setImageBitmap(diagnostic);
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
        if (audioMode) return;
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
        final boolean male=speaker==null?defaultKind==0:Boolean.TRUE.equals(characterGender.get(speaker));
        if(translateSwitch.isChecked()){
            final String fingerprint=cleaned;
            final long generation=translationGeneration;
            translateWithContext(cleaned, translated->{
                if(generation==translationGeneration && fingerprint.equals(lastSpoken) && !audioMode){
                    recognized.setText("Озвучка: "+translated);
                    speak(translated,male);
                }
            }, error->show("Ошибка перевода: "+error));
        } else speak(cleaned,male);
    }
    private void speak(String phrase, boolean male){
        if(!ttsReady||phrase.trim().isEmpty())return;
        tts.setLanguage(new Locale("ru","RU"));
        int index=male?maleIndex:femaleIndex;
        if(index>0&&index<=russianVoices.size())tts.setVoice(russianVoices.get(index-1));
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
        stopMicrophone();
        translationExecutor.shutdownNow();
        if (speechRecognizer != null) {speechRecognizer.destroy();speechRecognizer=null;}
        handler.removeCallbacksAndMessages(null);started=false;
        recognizer.close();cameraExecutor.shutdown();if(translator!=null)translator.close();if(tts!=null){tts.stop();tts.shutdown();}super.onDestroy();}
}
