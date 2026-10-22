# Rudin 全部習題的 Lean 4 形式化計畫

## Goal

使用 Lean 4 與 Mathlib，完成 `data/` 中 Walter Rudin 的 *Principles of Mathematical Analysis*, Third Edition 的全部章末習題，包含所有子題、反例、條件分類與題目指定的構造。

「完成」表示題意已覆核、答案完整、證明經 Lean kernel 檢查，且可從鎖定版本的乾淨環境重建。原敘述若不成立，交付原敘述的形式化反例及明確標示的修正版，而不是加入隱藏條件或嘗試證明錯誤命題。

使用者已授權執行本計畫。依題目相依關係分批實作，使用 subagent 平行盤點、解題及獨立覆核；未取得有效完成證據的任務保持開啟。

## Context

### 規劃時確認的教材與專案基線

- 主要來源：`data/Rudin - 1976 - Principles of Mathematical Analysis (International Series in Pure & Applied Mathematics).pdf`。
  - 351 個 PDF 頁面，標題頁註明 Third Edition，版權頁包含 1976。
  - SHA-256：`c0d8530ad52ff06bb3b949b4b27245c446cde045e70b3efcad0cd51804e938e7`。
  - 有 OCR 文字層，但題號、上下標、不等號與積分符號有辨識錯誤。
- 對照來源：`data/Walter Rudin - Principles of Mathematical Analysis.pdf`。
  - 同為 351 頁，已由頁面影像確認標題為 Third Edition；沒有可用的文字層。
  - 尚未逐頁核對兩份掃描；不假設所有頁面完全相同。
- `lean-toolchain` 鎖定 `leanprover/lean4:v4.35.0`。
- `lakefile.toml` 只有 `Math` library 與 `math` executable，沒有 Mathlib dependency。
- `Math/Basic.lean`、`Math.lean`、`Main.lean` 是 Hello World 範本，沒有現成習題證明。
- `.github/workflows/lean_action_ci.yml` 使用 `leanprover/lean-action@v1`，尚無題目覆蓋率及公理檢查。
- 規劃時已執行 `lake build`，範本建置成功；此結果不表示分析學基礎設施已可用。
- `.gitignore` 已忽略 `data/` 與 `.lake/`。不提交教材 PDF、整本 OCR 文字或頁面影像。

### 已盤點範圍

三個 subagent 分別核對第 1–4、5–8、9–11 章的完整習題段落與頁面影像；主代理補核 PDF 頁 30。`exercises.json` 目前記錄 287 題、839 個子義務，包含追問與已知原題問題的處置義務。這是來源盤點分母，不是完成解答數；後續若發現漏列義務，須附來源證據修正分母。

| 章 | 主題 | 題號範圍 | 書頁 | PDF 頁，從 1 起算 |
| --- | --- | --- | --- | --- |
| 1 | The Real and Complex Number Systems | 1–20 | 21–23 | 30–32 |
| 2 | Basic Topology | 1–30 | 43–46 | 52–55 |
| 3 | Numerical Sequences and Series | 1–25 | 78–82 | 87–91 |
| 4 | Continuity | 1–26 | 98–102 | 107–111 |
| 5 | Differentiation | 1–29 | 114–119 | 123–128 |
| 6 | The Riemann–Stieltjes Integral | 1–19 | 138–142 | 147–151 |
| 7 | Sequences and Series of Functions | 1–26 | 165–171 | 174–180 |
| 8 | Some Special Functions | 1–31 | 196–203 | 205–212 |
| 9 | Functions of Several Variables | 1–31 | 239–244 | 248–253 |
| 10 | Integration of Differential Forms | 1–32 | 288–299 | 297–308 |
| 11 | The Lebesgue Theory | 1–18 | 332–334 | 341–343 |

### 已發現的題意風險

- `R01E19`：書頁 23 要求球面半徑 `r > 0`，但沒有排除 `a = b`。退化情況須獨立處理，不能默默增加 `a ≠ b`。
- `R11E18`：書頁 334 將 Schwarz equality 寫成存在常數 `c` 使 `g = c f` almost everywhere；當 `f = 0` 而 `g ≠ 0` 時需要另行處理。
- 上述兩題現已完成 Lean 反例、修正版及獨立題意覆核，並在清單分別標為 `refuted_and_corrected`；不是原命題已證明。
- 其餘來源疑點仍在 `exercises.json` 與 `progress.md` 保留為 pending，不以這兩題的完成推論其他敘述正確。

### 本批執行結果（2026-10-22）

- 已驗證 8／287 題的解答處置、23／839 個義務：6 題按原敘述證明，2 題以反例與修正版完成；尚餘 279 題、816 個義務。
- `./scripts/check.sh` 通過：清單／import／declaration 檢查、預設建置、211 個 declaration 的公理檢查，以及 23 個回歸測試。
- 已在隔離的專案來源副本重建首批程式，使用新的 project build outputs，僅重用鎖定的 dependency cache。這不是全書 `--final` 驗收。
- `./scripts/check.sh --final` 仍正確失敗於未完成義務；不豁免全書完成門檻。遠端 CI 尚未執行。
- 目前的驗證狀態、來源／相依環境指紋與逐題覆核依據存於 `exercises.json`；摘要存於 `docs/rudin/progress.md`。本計畫尚未完成，須保留。

## Architecture

### 檔案與責任

沿用現有 `Math` library，不先改專案名稱，也不建立網站或資料庫。

```text
Math/Rudin/Chapter01/Exercise01.lean
...
Math/Rudin/Chapter11/Exercise18.lean
Math/Rudin/Support/<必要的共用主題>.lean
Math/Rudin.lean                         # 匯入全部交付模組
Math.lean                               # 匯入 Math.Rudin
exercises.json                          # 題目與子題清單、狀態、declaration 對照
scripts/check_exercises.py              # 覆蓋率、來源參照與 import 檢查
scripts/check_axioms.lean                # 檢查交付 declaration 的公理相依性
scripts/check.sh                         # 本機與 CI 的統一檢查入口
docs/rudin/source.md                     # 版本、頁碼、來源 hash
docs/rudin/formalization.md              # 題意轉換規則與共用表示法
docs/rudin/errata.md                     # 原敘述問題、反例與修正
docs/rudin/progress.md                   # 由清單產生的進度與阻塞摘要
```

- 每題一個主要檔案；同題子題共用必要的定義與局部 lemma。
- 只有確實跨題重用或需獨立驗證的基礎設施才放入 `Support/`。
- Lean namespace 使用 `Rudin.Chapter01` 等章別；declaration 使用 `exercise01`、`exercise01_a` 等可預測名稱。
- `exercises.json` 是覆蓋率與狀態的唯一資料來源。每題記錄 ID、章／題號、書頁／PDF 頁、簡短自述題意、子義務、模組、交付 declaration、相依項、狀態與驗證依據。
  - 有字母子題時沿用原標記；沒有標記的追問另給穩定 ID，例如 `R01E11.uniqueness`。
  - 不保存整本題目轉錄。正式數學敘述放在 Lean，差異與來源位置放在文件。
  - 狀態限於 `todo`、`in_progress`、`blocked`、`verified`；不能用「已寫敘述」或「已寫非形式解答」冒充 `verified`。
  - 已反駁的題目另記 disposition；不得把修正版標示為原命題已證明。

### 數學敘述契約

- 預設允許使用任何已在鎖定 Mathlib 中證明的定理，包括比書中當章更後面的結果。不要求重建整本課文，也不限制為初等證法。
  - 若題目明確要求構造、指定方法或驗證某個結構，仍須交付該構造及其性質，不能只引用存在性結果取代。
- 預設使用 Mathlib 的 `ℝ`、`ℂ`、metric spaces、filters、derivatives、measures 與 `Lp`；Rudin 的歐氏範數使用適當的 `EuclideanSpace` 表示，不把任意函數空間的預設範數當作歐氏範數。
- 每題先核對量詞、定義域、空集合、零維／低維、零向量、端點、索引起點、有限／可數、點態／almost everywhere 等條件，再寫證明。
- 開放式問句必須轉成完整義務：正向敘述、逆命題的判定、必要反例、等號成立條件及維度分類均不能省略。
- 題目若要求 quotient construction、Dedekind cuts 或特殊積分，使用 Mathlib 的成品前先核對是否保留了題目要求；必要時建立最小模型與比較定理。
- 原題有問題時，保留來源與差異，證明反例，並證明明確修正後的版本；不能修改來源敘述後假裝沒有變更。
- 禁止 `sorry`、`admit`、`sorryAx`、自訂公理，以及把待證結論藏進 hypothesis、typeclass 或定義。
- 最終交付與共用定理的傳遞公理相依性只允許標準 `propext`、`Classical.choice`、`Quot.sound`；使用其他信任機制須改寫證明，不自動放寬清單。
- 編譯成功只證明所寫敘述成立，不證明題意翻譯正確。逐題語義覆核是獨立完成條件。

### 平行執行規則

- 主代理獨占工具鏈、根 imports、`exercises.json`、驗證工具、CI 與本計畫的整合。
- Subagent 只修改分配的互斥檔案；需要共用定義時先回報，不自行更改其他工作者的接口。
- 來源盤點可與工具鏈準備平行；代表題及原題反例可在所需表示法穩定後平行處理。
- 第 6、10 章的探索先交付受限但真實的 prototype，明列缺口；缺少橋接的相依題目不展開批量解題。
- 解題者回報精確 declaration、編譯結果與未完成義務；獨立 subagent 覆核題意後，主代理才記錄驗證狀態。

## Plan

### P1 — 鎖定完整範圍與題意

- [x] 建立 `docs/rudin/source.md` 與 `exercises.json`，逐頁核對 11 章全部題號及所有追問；驗收：每一來源題目恰有一個主 ID，子義務可回溯到頁碼，章別總數與總分母一致。證據：三份來源盤點合併為 287 題／839 個義務；`scripts/check_exercises.py` 核對題號、子義務分母與書頁／PDF 頁偏移。來源覆核不代表 Lean 語義覆核完成。
- [ ] 逐題建立簡短語義契約、題型與相依項，並登記 OCR 疑點、缺漏條件及所需構造；驗收：全部題目均有可執行的形式化目標，高風險題有具體發現任務，不以未確認的定理名稱作前提。進度：全部題目已有來源契約與子義務；原題疑點及方法相依仍需釐清。
- [ ] 釐清清單中的全部 pending 來源問題，將定義慣例、開放式範圍與真正錯誤分開處置；驗收：每項有來源／上下文依據、明確的待證契約與相依義務，需反例的問題在完成 Lean 證明前不得標為已解決。

### P2 — 建立可重現的 Lean 與檢查基礎

- [x] 選定並鎖定實際相容的 Mathlib commit 與 Lean toolchain；驗收：提交 `lean-toolchain`、dependency 設定與 `lake-manifest.json`，執行 `lake update`、`lake exe cache get`、`lake build` 成功並保留版本證據。證據：維持 Lean 4.35.0，Mathlib v4.35.0 commit `56a005855ea17e0b0958f73ec801ae140b0a1679`；更新、下載 9031 個快取項目與預設 executable／library 建置均成功。
- [x] 建立 `Math/Rudin.lean`、最小範例與 `scripts/check.sh`；驗收：專案仍能從預設 build target 建置 library，`lake env lean <範例檔>` 成功，所有已交付模組都由 root import 納入。證據：首批 8 題與 3 個 Support 模組均由 root 公開匯入；單檔及預設 executable／library 建置成功。原範本同步改用 Lean module system，保留原 executable。
- [x] 實作清單、import、declaration 與公理檢查，接到現有 CI；驗收：正常範例通過，臨時負向 fixture 中的漏列子題、遺漏 import、不存在 declaration、`sorry` 及自訂公理均會失敗，fixture 不進入交付 library。證據：`./scripts/check.sh` 通過；23 個回歸測試包含實際 Lean environment 負向測試、失敗 evidence 與來源／共用定義／依賴變動失效測試；私有證明本體檢查涵蓋 211 個 declaration 與 31 個交付參照。CI 已設定相同入口，遠端 CI 未執行。
  - 檢查須使用 Lean environment／型別檢查，不只搜尋文字；公理檢查涵蓋交付與 Support declarations 的傳遞相依性。
  - 使用 Python 的檢查工具一律透過 `uv run python` 執行；有第三方依賴時須鎖定版本。
  - 開發期允許清單中有未完成題目；最終模式必須因任何非 `verified` 項目而失敗。
  - `verified` evidence 必須明確記錄成功結果、語義覆核者、局部來源 import closure 指紋與工具鏈／設定／manifest 指紋；失敗的非空資料不能算成功，共用定義或環境變動須使舊 evidence 失效。

### P3 — 先做高風險探索與代表題試作

本階段在展開全書解題前完成，避免做到第 10 章才發現需要大量新基礎設施。

- [x] 調查鎖定 Mathlib 的章別支援，建立「可直接用／需橋接／需新增」對照；驗收：每項引用有實際 source path 與可編譯使用例，特別涵蓋 Dedekind cuts、metric completion、Riemann–Stieltjes integral、ODE、Fourier／Gamma、differential forms／Stokes 及 `Lp`。證據：`docs/rudin/mathlib-coverage.md` 的來源對照與 `Support/ApiExamples.lean` 已編譯、納入根 imports 及全專案公理檢查；不宣稱已逐題完成 API 選型。
- [ ] 建立第 6 章積分表示法的可編譯 prototype；驗收：明確說明表示法如何涵蓋 Rudin 的 monotone integrator、discontinuities 與 endpoint conventions，完成一個等價性或適用條件下的橋接結果。不能未經證明就以 Lebesgue integral 取代 Riemann–Stieltjes integral。進度：實際 Darboux sums、常數 integrand 的橋接與右正規化端點反例已編譯；非定值 integrand 與完整端點處置仍未完成。
- [ ] 建立第 10 章所需基礎設施的可編譯 prototype；驗收：按實際習題需求檢查 differential forms、pullback、exterior derivative、chains、orientation 與 integration 的表示法，完成一個非平凡運算及一個實際所需的 integration／boundary identity，列出尚缺定理與相依順序。不預設 Mathlib 已具備整套 Stokes theory。進度：實際 `extDeriv` 計算與 segment／rectangle boundary identities 已編譯；一般 chains、simplex integration 與書中積分的比較仍未完成。
- [ ] 補齊第 6 章 partitions 的 common refinement、sum bounds 與 Darboux／tagged equivalence；驗收：有不依賴待證結論的 Lean 定理，並以定值及點支撐 integrand 檢查表示法。
- [ ] 建立第 6 章非定值 integrand 的積分橋接及必要 jump／endpoint 條件；驗收：至少覆蓋 continuous integrands 並形式化比較，既有端點反例仍成立，不放寬信任條件。
- [ ] 建立第 10 章所需的 signed affine／parameterized chains 與 face maps；驗收：證明 `∂² = 0`、面抵消與 multiplicity，並對照第 16–19、32 題的義務。
- [ ] 建立第 10 章 forms 的 pullback／simplex integration 與 Rudin 積分的比較；驗收：在所需規則性與方向條件下證明比較和 boundary identities，不用已假設的 Stokes identity 證明自身。
- [x] 完成代表題 `R01E01`、`R02E02`、`R03E24`、`R06E01`、`R09E01`、`R11E01` 的全部義務；驗收：每題語義覆核、編譯、公理檢查及清單對照均通過。證據：六題共 15 個義務均為 `verified`；獨立覆核確認實際 Cauchy-sequence quotient 與完備化橋接，以及實際 Darboux 積分。R06E01 首輪發現嚴格 partition／零長區間漏列，已修正成 weak partition 與 `a ≤ b`，第二輪獨立覆核、singleton／endpoint 測試及整合檢查均通過。
- [ ] 根據 prototype 與代表題更新此計畫、共用表示法及章別工作量；驗收：重大缺口拆成可執行任務，未解決的正確性問題明確阻塞受影響題目，時程估計只依實測分類，不宣稱各題成本相同。

### P4 — 驗證已知原題問題

- [x] 完成 `R01E19` 的退化情況反例、非退化版本及完整分類；驗收：Lean 驗證來源問題與修正後結果，`errata.md` 記錄原條件、修正及對應 declaration。證據：4 個義務通過獨立覆核與整合檢查；反例排除所有可能的正半徑球面，不只檢查原公式。
- [x] 完成 `R11E18` 的零函數反例與完整 Schwarz equality 條件；驗收：Lean 驗證反例與包含退化情況的正確版本，不以額外非零假設掩蓋來源問題。證據：4 個義務通過獨立覆核與整合檢查；已證明 complex L2／原積分橋接、完整零函數分支與有限 Dirac measure 反例。

### P5 — 依章完成全部題目

以下每項均只處理尚未完成的題目；P3、P4 的成果不重複計數。章順序是預設順序，實際以清單中的題目相依關係為準。每批以 3–5 題為起點，大型構造題單獨處理。

- [ ] 完成第 1 章 1–20 題；驗收：全部子義務通過本節的逐批門檻，包含複數根、等號條件、維度分類與修改 cuts 定義的構造。
- [ ] 完成第 2 章 1–30 題；驗收：全部子義務通過逐批門檻，並明確區分有限、至多可數與可數無限。
- [ ] 完成第 3 章 1–25 題；驗收：全部子義務通過逐批門檻，包含完備化構造、稠密嵌入與相關識別結果。
- [ ] 完成第 4 章 1–26 題；驗收：全部子義務通過逐批門檻，逆命題及移除假設的問題均有判定與所需反例。
- [ ] 完成第 5 章 1–29 題；驗收：全部子義務通過逐批門檻，端點導數、ODE uniqueness 與指定初始條件語義一致。
- [ ] 完成第 6 章 1–19 題；驗收：全部子義務通過逐批門檻，積分存在性、積分值及 rectifiable curves 的要求均有對應結果。
- [ ] 完成第 7 章 1–26 題；驗收：全部子義務通過逐批門檻，uniform convergence、equicontinuity 與 ODE existence 的型別及定義域一致。
- [ ] 完成第 8 章 1–31 題；驗收：全部子義務通過逐批門檻，涵蓋 Fourier、Gamma、winding number、fixed point 與 asymptotics，不只完成初等函數題。
- [ ] 完成第 9 章 1–31 題；驗收：全部子義務通過逐批門檻，linear maps、Fréchet derivatives、Jacobian 與 Taylor polynomial 的表示法有明確對照。
- [ ] 完成第 10 章 1–32 題；驗收：全部子義務通過逐批門檻，包含參數方向、boundary multiplicity、orientation 及非 orientable 情況，不用幾何直覺代替證明。
- [ ] 完成第 11 章 1–18 題；驗收：全部子義務通過逐批門檻，明確區分函數與 almost-everywhere equivalence classes，涵蓋 measure construction 與 completeness 的指定要求。

每批完成前依序執行：

1. 對照 PDF 頁面覆核所有子義務；先完成必要的非形式推導，再確認 Lean 型別。
2. 搜尋已鎖定 Mathlib；先使用現有結果，只新增確實缺少的 lemma 或構造。
3. 執行單檔 `lake env lean <檔案>`、全專案 `lake build` 與 `./scripts/check.sh`。
4. 覆核實際 elaborated declaration type，確認沒有錯誤預設實例、未使用假設、弱化結論或真空成立的前提；保留逐題覆核依據。
5. 僅在以上檢查通過後更新為 `verified`，重建 `progress.md`，並更新本計畫的有效完成證據。發現新 erratum 時依 P4 的同一標準處理。

### P6 — 全書整合驗收

- [ ] 對全部題目進行第二輪語義覆核，重新對照頁面、量詞與子題完整性；驗收：每個子義務有實際 declaration 或明確形式化答案，所有原題問題均有反例及修正證據，未解決問題維持阻塞。
- [ ] 在隔離工作副本或乾淨 checkout 重建全部成果；驗收：僅由鎖定依賴執行 `lake exe cache get`、`lake build`、`./scripts/check.sh --final` 成功，沒有依靠原工作目錄的未追蹤檔案或本機自訂套件。
- [ ] 更新 `README.md`、來源文件及最終進度，寫明重建命令、題目索引、依賴版本與 errata 的計數方式；驗收：總題數與總子義務數均由清單計算，證明原題與反駁／修正原題分開報告。

## Completion Checklist

- [x] 11 章所有來源題目與子義務均完成核對，正式總數有來源依據。證據：`exercises.json` 的 287 題／839 個義務與 `source.md`；839 包含追問及已知錯誤的處置義務。這項來源盤點不表示題意問題全部解決或 Lean 證明全部完成。
- [ ] 全部義務均為 `verified`，沒有 `todo`、`in_progress`、`blocked` 或未完成的構造／追問。
- [ ] 原題不成立的情況有 Lean 反例與標示清楚的正確替代結果；沒有將錯誤原命題計為已證明。
- [x] 全部目前交付模組納入預設建置；不存在以未匯入檔案隱藏未完成證明的情況。證據：來源檔案 import closure 與實際 Lean environment 模組檢查均通過；新增檔案後須重跑。
- [x] 全部目前交付與 Support declarations 通過公理檢查，無佔位證明、自訂公理或未授權的信任擴充。證據：211 個 declaration 的傳遞相依只含 `propext`、`Classical.choice`、`Quot.sound`；新增或修改來源後須重跑。
- [ ] 逐題語義覆核與第二輪全書覆核均有記錄，所有重大正確性疑問已解決。
- [ ] 乾淨環境的全專案建置與最終檢查通過；本機與 CI 使用相同檢查入口，遠端 CI 執行結果若尚未取得則明確記錄，不宣稱已通過。
- [ ] 文件足以重建、定位題目及理解敘述差異，未提交教材 PDF、整本 OCR 或其他非必要二進位檔。

## Non-Goals

- 不重做 Mathlib 已有的整套實數、拓樸、微積分或 measure theory；題目明確要求的構造除外。
- 不把教科書每個定理都列為獨立交付目標；只補足習題所需結果。
- 不提供只有自然語言或只有 theorem skeleton 的「完成解答」。
- 不自行建立 Git commit、推送分支或觸發遠端操作；本地實作與依賴準備已由執行授權涵蓋。
- 不承諾未經代表題量測的固定總工期，也不把第 6、10 章的基礎設施成本當成已知小量。

## Risks

- **Mathlib 相容性與 API 支援未知**：P2 鎖定實際可用版本，P3 以編譯例證明支援情況；不依賴猜測的 API。
- **第 6、10 章可能需要大量新增基礎設施**：P3 提前驗證表示法與必要結果。未解決的橋接或定理缺口阻塞相依題目，不以 `axiom` 暫代。
- **原書敘述及 OCR 可能有誤**：題意以頁面影像為準；已知與新增問題均須形式化處置。
- **編譯成功但證明錯題**：每題保留語義契約與覆核依據，最終再做全書覆核；coverage 工具不能取代數學語義檢查。
- **規模與進度失真**：同時報告主題目完成數與子義務完成數，另列反駁／修正的原題；不以檔案數、行數或已宣告 theorem 數代替完成率。
- **長期 dependency drift**：全程使用鎖定版本；需要升級時另行驗證全部既有證明，不與新題目混做未驗證的大幅變動。
