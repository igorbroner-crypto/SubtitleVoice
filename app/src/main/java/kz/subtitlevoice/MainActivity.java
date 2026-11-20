package kz.subtitlevoice;

import android.Manifest;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.RectF;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
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
import java.util.regex.*;

/** Camera->cropped OCR->optional offline translation->speech. No screenshot storage. */
public class MainActivity extends AppCompatActivity {
    private final Handler handler = new Handler(Looper.getMainLooper());
    private final TextRecognizer recognizer = TextRecognition.getClient(TextRecognizerOptions.DEFAULT_OPTIONS);
    private final Map<String, Boolean> characterGender = new LinkedHashMap<>();
    private final ArrayList<Voice> russianVoices = new ArrayList<>();
    private SharedPreferences prefs;
    private PreviewView preview;
    private RoiOverlay overlay;
    private TextView status, recognized, speedLabel, namesLabel;
    private Spinner maleSpinner, femaleSpinner, defaultSpinner;
    private Switch translateSwitch;
    private TextToSpeech tts;
    private Translator translator;
    private boolean translatorReady = false, ttsReady = false, started = false, busy = false;
    private int attempts = 0, framesSinceText = 0;
    private String candidate = "", lastSpoken = "";
    private long lastSpokenAt = 0;
    private float widthFrac = .82f, heightFrac = .17f, centerYFrac = .80f, speechRate = 1.25f;
    private int maleIndex = 0, femaleIndex = 0, defaultKind = 0;
    private final Pattern characterTag = Pattern.compile("^\\s*([\\p{L}][\\p{L} ._'-]{0,30})\\s*[:：]\\s*(.+)$", Pattern.DOTALL);
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
        loadCharacters();
        buildUi();
        tts = new TextToSpeech(this, code -> handler.post(() -> {
            ttsReady = code == TextToSpeech.SUCCESS;
            if (ttsReady) { tts.setLanguage(new Locale("ru", "RU")); populateVoices(); }
            else show("Не найден движок озвучки Android");
        }));
        TranslatorOptions options = new TranslatorOptions.Builder()
            .setSourceLanguage(TranslateLanguage.ENGLISH).setTargetLanguage(TranslateLanguage.RUSSIAN).build();
        translator = Translation.getClient(options);
        if (translateSwitch.isChecked()) prepareTranslator();
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) startCamera();
        else cameraPermission.launch(Manifest.permission.CAMERA);
    }

    private int dp(float value) { return (int)(getResources().getDisplayMetrics().density * value + .5f); }
    private TextView text(String s, int sp) { TextView t = new TextView(this); t.setText(s); t.setTextColor(Color.WHITE); t.setTextSize(sp); t.setPadding(dp(4),dp(6),dp(4),dp(6)); return t; }
    private LinearLayout.LayoutParams full() { return new LinearLayout.LayoutParams(-1, -2); }
    private void add(LinearLayout l, View v) { l.addView(v,full()); }
    private void buildUi() {
        LinearLayout root = new LinearLayout(this); root.setOrientation(LinearLayout.VERTICAL); root.setBackgroundColor(Color.rgb(13,18,29));
        ScrollView scroll = new ScrollView(this); root.addView(scroll);
        LinearLayout content = new LinearLayout(this); content.setOrientation(LinearLayout.VERTICAL); content.setPadding(dp(12), dp(10), dp(12), dp(18)); scroll.addView(content);
        add(content, text("SUBTITLE VOICE   •   Камера → голос", 19));
        FrameLayout stage = new FrameLayout(this);
        stage.setBackgroundColor(Color.BLACK);
        add(content, stage);
        stage.getLayoutParams().height = dp(300);
        preview = new PreviewView(this);
        preview.setScaleType(PreviewView.ScaleType.FILL_CENTER);
        stage.addView(preview, new FrameLayout.LayoutParams(-1,-1));
        overlay = new RoiOverlay(); stage.addView(overlay,new FrameLayout.LayoutParams(-1,-1));
        add(content, text("Распознаётся ТОЛЬКО область внутри рамки. Наведи камеру на центр нижней части ТВ.", 12));
        status = text("Инициализация…", 13); add(content,status);
        recognized = text("Последняя реплика: —", 14); add(content,recognized);
        Button toggle = new Button(this); toggle.setText("Пауза распознавания"); add(content,toggle);
        toggle.setOnClickListener(v -> { started = !started; toggle.setText(started ? "Пауза распознавания" : "Продолжить распознавание"); if (!started && tts != null) tts.stop(); });
        add(content,text("Область субтитров",16));
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
        add(content,text("Привязка голоса по имени (например, Маша: Привет)",16));
        namesLabel=text("",13);add(content,namesLabel); renderNames();
        EditText nameInput = new EditText(this);nameInput.setTextColor(Color.WHITE);nameInput.setHintTextColor(0xffaaaaaa);nameInput.setHint("Имя персонажа: Маша");nameInput.setSingleLine(true);add(content,nameInput);
        Spinner gender = new Spinner(this);gender.setAdapter(new ArrayAdapter<>(this, android.R.layout.simple_spinner_dropdown_item,new String[]{"Мужской", "Женский"}));add(content,gender);
        Button addName = new Button(this);addName.setText("Добавить / изменить персонажа");add(content,addName);
        addName.setOnClickListener(v -> {
            String n=nameInput.getText().toString().trim().toLowerCase(Locale.ROOT);
            if(n.isEmpty())return;
            characterGender.put(n,gender.getSelectedItemPosition()==0);saveCharacters();renderNames();nameInput.setText("");
        });
        Button remove = new Button(this);remove.setText("Удалить персонажа по имени");add(content,remove);
        remove.setOnClickListener(v->{String n=nameInput.getText().toString().trim().toLowerCase(Locale.ROOT); characterGender.remove(n);saveCharacters();renderNames();});
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
    private void loadCharacters(){String raw=prefs.getString("characters","Вася|1;Петя|1;Маша|0;Марина|0");
        for(String item:raw.split(";")){String[] a=item.split("\\|",2);if(a.length==2)characterGender.put(a[0].toLowerCase(Locale.ROOT),"1".equals(a[1]));}}
    private void saveCharacters(){StringBuilder b=new StringBuilder();for(Map.Entry<String,Boolean> e:characterGender.entrySet()){
        if(b.length()>0)b.append(';');b.append(e.getKey()).append('|').append(e.getValue()?1:0);
    }prefs.edit().putString("characters",b.toString()).apply();}
    private void renderNames(){StringBuilder b=new StringBuilder();for(Map.Entry<String,Boolean> e:characterGender.entrySet()){
        if(b.length()>0)b.append("  •  ");b.append(e.getKey()).append(" — ").append(e.getValue()?"муж.":"жен.");
    }namesLabel.setText(b.length()==0?"Пока нет персонажей":b.toString());}
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
    private void startCamera(){
        ListenableFuture<ProcessCameraProvider> future=ProcessCameraProvider.getInstance(this);
        future.addListener(()->{
            try{
                ProcessCameraProvider provider=future.get();provider.unbindAll();
                Preview p=new Preview.Builder().build();p.setSurfaceProvider(preview.getSurfaceProvider());
                provider.bindToLifecycle(this,CameraSelector.DEFAULT_BACK_CAMERA,p);
                started=true;show("Камера готова — наведи на субтитры");handler.postDelayed(scanLoop,350);
            }catch(Exception ex){show("Ошибка камеры: "+ex.getMessage());}
        }, ContextCompat.getMainExecutor(this));
    }
    private final Runnable scanLoop = new Runnable(){@Override public void run(){
        if(isFinishing()||isDestroyed())return;
        if(started&&!busy)captureAndRecognize();
        handler.postDelayed(this,260);
    }};
    private void captureAndRecognize(){
        Bitmap bitmap=preview.getBitmap();
        if(bitmap==null||bitmap.getWidth()<100||bitmap.getHeight()<100)return;
        int w=bitmap.getWidth(),h=bitmap.getHeight();
        int rw=Math.max(16,(int)(w*widthFrac)),rh=Math.max(16,(int)(h*heightFrac));
        int left=Math.max(0,Math.min(w-rw,(w-rw)/2));
        int top=Math.max(0,Math.min(h-rh,(int)(h*centerYFrac-rh/2f)));
        Bitmap cropped;
        try {
            cropped = Bitmap.createBitmap(rw,rh,Bitmap.Config.ARGB_8888);
            Canvas cropCanvas = new Canvas(cropped);
            cropCanvas.drawBitmap(bitmap,-left,-top,null);
        } catch(Exception e) {bitmap.recycle();return;}
        bitmap.recycle();
        busy=true;
        recognizer.process(InputImage.fromBitmap(cropped,0))
          .addOnSuccessListener(result->{
              StringBuilder s=new StringBuilder();
              for(com.google.mlkit.vision.text.Text.TextBlock block:result.getTextBlocks()){
                  if(s.length()>0)s.append(' ');s.append(block.getText().replace('\n',' '));
              }
              onRecognition(s.toString().trim());
          }).addOnFailureListener(e->show("Ошибка OCR: "+e.getMessage()))
          .addOnCompleteListener(task->{busy=false;cropped.recycle();});
    }
    private void onRecognition(String raw){
        String cleaned=raw.replaceAll("\\s+"," ").trim();
        if(cleaned.length()<2){framesSinceText++;if(framesSinceText>=3){candidate="";lastSpoken="";}return;}
        framesSinceText=0;
        if(cleaned.equalsIgnoreCase(candidate)) attempts++; else{candidate=cleaned;attempts=1;}
        if(attempts<2)return; // Two matching consecutive frames suppress visual noise.
        if(cleaned.equalsIgnoreCase(lastSpoken))return;
        if(System.currentTimeMillis()-lastSpokenAt<350)return;
        lastSpoken=cleaned;lastSpokenAt=System.currentTimeMillis();
        String speaker=null;String payload=cleaned;
        Matcher m=characterTag.matcher(cleaned);
        if(m.matches()){
            String key=m.group(1).trim().toLowerCase(Locale.ROOT);
            if(characterGender.containsKey(key)){speaker=key;payload=m.group(2).trim();}
        }
        if(payload.isEmpty())return;
        final boolean male=speaker==null?defaultKind==0:Boolean.TRUE.equals(characterGender.get(speaker));
        final String sourceText=payload;
        recognized.setText("Распознано: "+cleaned);
        if(translateSwitch.isChecked()){
            if(!translatorReady){show("Ожидаю загрузку модели перевода…");return;}
            final String fingerprint=cleaned;
            translator.translate(sourceText).addOnSuccessListener(translated->{
                if(fingerprint.equals(lastSpoken)){
                    recognized.setText("Озвучка: "+translated);speak(translated,male);
                }
            }).addOnFailureListener(e->{show("Ошибка перевода: "+e.getMessage());});
        } else speak(sourceText,male);
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
    @Override protected void onDestroy(){handler.removeCallbacksAndMessages(null);started=false;
        recognizer.close();if(translator!=null)translator.close();if(tts!=null){tts.stop();tts.shutdown();}super.onDestroy();}
}
