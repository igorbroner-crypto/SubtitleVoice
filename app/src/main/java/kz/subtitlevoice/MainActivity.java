package kz.subtitlevoice;

import android.Manifest;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.Rect;
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
    private String activeSpeaker = null;
    private long activeSpeakerUntil = 0;
    private long lastSpokenAt = 0;
    private float widthFrac = .82f, heightFrac = .17f, centerYFrac = .80f, speechRate = 1.25f;
    private int maleIndex = 0, femaleIndex = 0, defaultKind = 0, contrastMode = 1;
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
        contrastMode = prefs.getInt("contrastMode", 1);
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
        add(content,text("Контраст субтитров на фоне игры",16));
        add(content,text("Если у субтитров нет чёрной подложки, попробуй режим «Светлые буквы». Он выделяет текст относительно окружающего фона.",12));
        Spinner contrastSpinner = new Spinner(this);
        contrastSpinner.setAdapter(new ArrayAdapter<>(this, android.R.layout.simple_spinner_dropdown_item,
            new String[]{"Без обработки", "Светлые буквы на пёстром фоне", "Тёмные буквы на пёстром фоне"}));
        contrastSpinner.setSelection(contrastMode);
        contrastSpinner.setOnItemSelectedListener(new SpinnerListener(i -> {
            contrastMode=i; prefs.edit().putInt("contrastMode",i).apply();
        }));
        add(content,contrastSpinner);
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
        add(content,text("Привязка голоса по имени: отдельная подпись сверху/слева, имя перед тире или двоеточием",16));
        add(content,text("Имена отделяются от реплик до перевода и озвучки. Для подписи другим цветом имя нужно добавить в список персонажей; без подписи используется голос по умолчанию.",12));
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
        final Bitmap processed;
        try {
            processed = contrastMode == 0 ? cropped : enhanceSubtitleText(cropped, contrastMode == 1);
        } catch (Exception ex) {
            cropped.recycle(); busy=false; show("Ошибка обработки кадра: " + ex.getMessage()); return;
        }
        recognizer.process(InputImage.fromBitmap(processed,0))
          .addOnSuccessListener(result -> {
              SubtitleData data=extractSubtitle(result);
              if (!data.speech.isEmpty() || !data.speaker.isEmpty() || processed == cropped) {
                  onRecognition(data);
                  busy=false;
                  processed.recycle();
                  if (processed != cropped) cropped.recycle();
              } else {
                  // Only if contrast enhancement fails to find any letters, try the original.
                  recognizer.process(InputImage.fromBitmap(cropped,0))
                    .addOnSuccessListener(original -> onRecognition(extractSubtitle(original)))
                    .addOnFailureListener(e -> show("Ошибка OCR: " + e.getMessage()))
                    .addOnCompleteListener(t -> {busy=false;processed.recycle();cropped.recycle();});
              }
          })
          .addOnFailureListener(e -> {
              show("Ошибка OCR: " + e.getMessage());
              busy=false; processed.recycle(); if(processed != cropped) cropped.recycle();
          });
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

    private void onRecognition(SubtitleData data){
        String cleaned=data.speech.replaceAll("\\s+"," ").trim();
        if(!data.speaker.isEmpty()){
            activeSpeaker=data.speaker;
            activeSpeakerUntil=System.currentTimeMillis()+2500;
        }
        if(cleaned.length()<2){framesSinceText++;if(framesSinceText>=3){candidate="";lastSpoken="";}return;}
        framesSinceText=0;
        String speaker = !data.speaker.isEmpty() ? data.speaker :
            System.currentTimeMillis()<activeSpeakerUntil ? activeSpeaker : null;
        if(cleaned.equalsIgnoreCase(candidate)) attempts++; else{candidate=cleaned;attempts=1;}
        if(attempts<2)return;
        if(cleaned.equalsIgnoreCase(lastSpoken))return;
        if(System.currentTimeMillis()-lastSpokenAt<350)return;
        lastSpoken=cleaned;lastSpokenAt=System.currentTimeMillis();
        final boolean male=speaker==null?defaultKind==0:Boolean.TRUE.equals(characterGender.get(speaker));
        recognized.setText("Реплика: "+cleaned+(speaker==null?"":"  ["+speaker+"]"));
        if(translateSwitch.isChecked()){
            if(!translatorReady){show("Ожидаю загрузку модели перевода…");return;}
            final String fingerprint=cleaned;
            translator.translate(cleaned).addOnSuccessListener(translated->{
                if(fingerprint.equals(lastSpoken)){
                    recognized.setText("Озвучка: "+translated);speak(translated,male);
                }
            }).addOnFailureListener(e->{show("Ошибка перевода: "+e.getMessage());});
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
    @Override protected void onDestroy(){handler.removeCallbacksAndMessages(null);started=false;
        recognizer.close();if(translator!=null)translator.close();if(tts!=null){tts.stop();tts.shutdown();}super.onDestroy();}
}
