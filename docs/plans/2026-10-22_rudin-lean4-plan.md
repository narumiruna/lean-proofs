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

三個 subagent 分別核對第 1–4、5–8、9–11 章的完整習題段落與頁面影像；主代理補核 PDF 頁 30。`exercises.json` currently records 287 exercises and 849 obligations, including follow-up questions and source-issue dispositions. The initial 839 obligations gained eight explicit checks in the second batch, R03E14's zero-bound strict-estimate obstruction in the fourth batch, and the printed R06E02 comparison in the seventh batch. Evidence is in `docs/rudin/source-clarifications.md`.這是來源盤點分母，不是完成解答數；後續若發現漏列義務，須附來源證據修正分母。

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

### 第一批執行結果（2026-10-22）

- 已驗證 8／287 題的解答處置、23／839 個義務：6 題按原敘述證明，2 題以反例與修正版完成；尚餘 279 題、816 個義務。
- `./scripts/check.sh` 通過：清單／import／declaration 檢查、預設建置、211 個 declaration 的公理檢查，以及 23 個回歸測試。
- 已在隔離的專案來源副本重建首批程式，使用新的 project build outputs，僅重用鎖定的 dependency cache。這不是全書 `--final` 驗收。
- `./scripts/check.sh --final` 仍正確失敗於未完成義務；不豁免全書完成門檻。遠端 CI 尚未執行。
- 目前的驗證狀態、來源／相依環境指紋與逐題覆核依據存於 `exercises.json`；摘要存於 `docs/rudin/progress.md`。本計畫尚未完成，須保留。

### 第二批執行結果（2026-10-22）

- 新增完成第 1 章剩餘 18 題；該章 20／20 題、55／55 個義務均已驗證。全書目前 26／287 題、72／847 個義務；24 題按原敘述證明，2 題以反例及修正版處置。尚餘 261 題、775 個義務。
- 完成來源問題的 discovery：15 題／18 個問題有明確契約，新增 8 個原先未獨立追蹤的 domain／convention／obstruction 義務，沒有移除原義務。相關數學證明仍為 todo／pending，不把契約選定當作解題完成。
- 新增 Stieltjes common refinement、sum bounds、完整 Darboux／tagged equivalence、raw monotone continuous-integrand existence，以及 explicit right-continuous measure bridge；另有受限 raw ordered-chain boundary 基礎。所有適用範圍及未完成比較見 `mathlib-coverage.md`。
- `./scripts/check.sh` 與使用 fresh project build outputs 的隔離來源副本檢查均通過：538 個 declaration、104 個交付參照及 23 個回歸測試；只重用鎖定的 dependency cache。
- `./scripts/check.sh --final` 仍失敗於 `R02E01.empty_subset`，這是尚未完成的全書義務，不豁免最終門檻。遠端 CI 未執行。本計畫尚未完成並繼續保留。

### Third execution batch (2026-10-22)

- Completed the remaining 29 exercises in Chapter 2. The chapter now has 30/30 verified resolutions and 71/71 verified obligations. The book total is 55/287 resolutions and 142/847 obligations; 232 exercises and 705 obligations remain open.
- Of the 55 resolutions, 52 prove the source claim as stated and 3 retain a refutation and explicit correction. The third correction is the bounded-only reading of R02E29. Its extended interval convention is stated separately. R02E28 preserves Rudin's countably-infinite convention; its empty-set check is a translation check, not a source erratum.
- Every new exercise passed independent page-to-type review, single-file compilation, default project build, coverage and origin checks, and the proof-body axiom audit. The full current audit covers 991 local declarations and 185 delivery references. All 23 regression tests pass.
- Added a boundary-stable orientation quotient, fixed-degree boundaries, affine face comparisons, signed square/cube identities, and actual parameterized-square/Möbius seam multiplicities. Independent model checks prove infinite-order generators and retained seam multiplicity. General smooth simplex chains, geometric orientation/coverage, form integration and comparison with Rudin remain open; P3 is not complete.
- An isolated source copy ran `lake exe cache get` and `./scripts/check.sh` successfully with fresh project outputs, reusing only the pinned dependency cache. The cache confirmed all 9031 entries. This is batch validation, not full-book acceptance.
- `./scripts/check.sh --final` still fails correctly at `R03E01.absolute_values`. Remote CI has not run. This plan remains active and must be retained.

### Fourth execution batch (2026-10-22)

- Completed the remaining 24 exercises in Chapter 3. The chapter now has 25/25 resolutions and 89/89 obligations. The book total is 79/287 resolutions and 223/848 obligations; 208 exercises and 625 obligations remain open.
- Added one source-backed obligation for R03E14(e): the printed strict estimate fails for the allowed bound `M=0`. The constant-sequence obstruction, non-strict correction and strict `M>0` result are proved. The final Tauberian converse remains valid. All ten original obligations remain.
- Of the 79 resolutions, 75 are as stated and 4 retain a refutation/correction. R03E06 separates undefined parameters from divergence. R03E18 retains the inherited square-root starting bound and the possible first-step overshoot. Ordinary conditional series are not replaced by unconditional `Summable` assumptions.
- Independent page/type reviews cover every new obligation. Default project checks and an isolated-source rebuild pass for 1356 local declarations, 280 delivery references and 23 regression tests. The isolated copy ran `lake exe cache get`, `lake build`, and `./scripts/check.sh` with fresh project outputs and only the pinned dependency cache reused.
- The first integration audit rejected generated unsafe recursion helpers in the three Newton iterations. Explicit `Nat.rec` definitions and safe equations remove them. Final independent review and the unchanged strict project gate pass; no exception was added.
- `./scripts/check.sh --final` still fails correctly at `R04E01.symmetric_difference_converse`. Remote CI has not run. General Chapter 10 integration infrastructure and all remaining chapters stay open; this plan is retained.

### Fifth execution batch (2026-10-22)

- Completed Chapter 4: 26/26 resolutions and 74/74 obligations. The book total is 105/287 resolutions and 297/848 obligations; 182 exercises and 551 obligations remain open. Of the completed resolutions, 101 are as stated and 4 retain refutations/corrections.
- Every new exercise has independent page-to-type review, compilation and current project evidence. Includes all affine-line counterexamples, explicit Cauchy-sequence extension, rational triples for all simple discontinuities, literal Thomae values, complete-range cases, extended-diameter conventions and required compact-subsequence arguments. R04E09's convention is resolved without a source-refutation count.
- Added real Stieltjes algebra, absolute-value existence/bounds and full interval joining/restriction with raw endpoints. Added genuine path-quotient integration, actual exterior-derivative comparison and a source-Darboux boundary identity. Independent review passed both modules, with 30 and 22 additional model checks respectively. No Chapter 6 or general Chapter 10 exercise is counted complete from infrastructure alone.
- `./scripts/check.sh` and an isolated-source rebuild pass: 1692 local declarations, 367 delivery references and 23 regression tests. The isolated copy ran cache retrieval, the default build and the shared check entry point with fresh project outputs. All nine dependency checkouts match the locked revisions and have clean worktrees.
- `./scripts/check.sh --final` still fails correctly at `R05E01.constant`. Remote CI has not run. Products/complex Stieltjes integrands, improper limits, general smooth simplex integration and higher-dimensional Stokes remain open. This plan remains active.

### Sixth execution batch (2026-10-22)

- Completed Chapter 5: 29/29 resolutions and 84/84 obligations. The book total is 134/287 resolutions and 381/848 obligations; 153 exercises and 467 obligations remain open. Of the completed resolutions, 128 are as stated and 6 retain obstructions/refutations and corrections.
- Independent source/type/body reviews cover every new obligation. Closed-interval derivatives remain one-sided. Genuine derivative jets prevent default-zero higher-derivative shortcuts. Includes all seven sharp oscillatory thresholds, exact Landau suprema and vector bounds, actual fixed-point orbits and diagrams, full Newton termination corrections, and complete forward square-root ODE classification and system uniqueness.
- R05E13 retains the printed negative-base obstruction and proves the explicitly labelled absolute-power correction. R05E25 retains the affine termination counterexample, absorbing iteration and separate zero-curvature estimates. A follow-up review verifies that R05E24's two comment changes clarify scalar side reversal without changing any proof or contract.
- Added continuous composition and product existence for raw Stieltjes integrals, plus actual complex tagged sums, component equivalence, norm integrability/bounds, algebra and full interval splitting. Independent reviews include 35 and 33 model checks. General discontinuous-integrand measure comparisons, vector integrands, improper integration and integration by parts remain open.
- Current project and isolated-source checks pass: 2241 local declarations, 504 delivery references and 23 regression tests. The isolated copy retrieved the locked cache, rebuilt fresh project outputs, and ran the shared check entry point. All nine dependency revisions match the manifest and have clean worktrees. These audit counts include R06E02, which remains in_progress and is not counted complete.
- `./scripts/check.sh --final` still fails correctly at `R06E02.vanishing`. Remote CI has not run. Chapter 6 work has started; Chapters 7–11 and the remaining geometric infrastructure stay open. This plan remains active.

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
- [x] 逐題建立簡短語義契約、題型與相依項，並登記 OCR 疑點、缺漏條件及所需構造；驗收：全部題目均有可執行的形式化目標，高風險題有具體發現任務，不以未確認的定理名稱作前提。證據：287 題均有來源契約與子義務；15 題的明確修正／慣例／有限延伸契約已記錄於清單與 `source-clarifications.md`，並通過獨立 discovery 覆核。
- [x] 釐清清單中的全部 pending 來源問題，將定義慣例、開放式範圍與真正錯誤分開處置；驗收：每項有來源／上下文依據、明確的待證契約與相依義務，需反例的問題在完成 Lean 證明前不得標為已解決。證據：18 個問題均有書頁／PDF 頁、影像／上下文依據及明確待證契約；新增 8 個漏列義務且未移除原義務。數學反例與修正版尚未證明的問題仍保持 pending；不新增外部接受或人工審批門檻。

### P2 — 建立可重現的 Lean 與檢查基礎

- [x] 選定並鎖定實際相容的 Mathlib commit 與 Lean toolchain；驗收：提交 `lean-toolchain`、dependency 設定與 `lake-manifest.json`，執行 `lake update`、`lake exe cache get`、`lake build` 成功並保留版本證據。證據：維持 Lean 4.35.0，Mathlib v4.35.0 commit `56a005855ea17e0b0958f73ec801ae140b0a1679`；更新、下載 9031 個快取項目與預設 executable／library 建置均成功。
- [x] 建立 `Math/Rudin.lean`、最小範例與 `scripts/check.sh`；驗收：專案仍能從預設 build target 建置 library，`lake env lean <範例檔>` 成功，所有已交付模組都由 root import 納入。證據：首批 8 題與 3 個 Support 模組均由 root 公開匯入；單檔及預設 executable／library 建置成功。原範本同步改用 Lean module system，保留原 executable。
- [x] 實作清單、import、declaration 與公理檢查，接到現有 CI；驗收：正常範例通過，臨時負向 fixture 中的漏列子題、遺漏 import、不存在 declaration、`sorry` 及自訂公理均會失敗，fixture 不進入交付 library。證據：`./scripts/check.sh` 通過；23 個回歸測試包含實際 Lean environment 負向測試、失敗 evidence 與來源／共用定義／依賴變動失效測試；私有證明本體檢查涵蓋 211 個 declaration 與 31 個交付參照。CI 已設定相同入口，遠端 CI 未執行。
  - 檢查須使用 Lean environment／型別檢查，不只搜尋文字；公理檢查涵蓋交付與 Support declarations 的傳遞相依性。
  - 使用 Python 的檢查工具一律透過 `uv run python` 執行；有第三方依賴時須鎖定版本。
  - 開發期允許清單中有未完成題目；最終模式必須因任何非 `verified` 項目而失敗。
  - `verified` evidence 必須明確記錄成功結果、語義覆核者、局部來源 import closure 指紋與工具鏈／設定／manifest 指紋；失敗的非空資料不能算成功，共用定義或環境變動須使舊 evidence 失效。

### P3 — 先做高風險探索與代表題試作

本階段在展開依賴高風險基礎設施的全書題組前完成，避免做到第 10 章才發現需要大量新基礎設施。探索期間可平行完成定義已確定、且不依賴缺口的基礎題組；第二批已完成第 1 章。後續仍按相依關係選題，不豁免第 6／10 章所需的橋接與方向條件。

- [x] 調查鎖定 Mathlib 的章別支援，建立「可直接用／需橋接／需新增」對照；驗收：每項引用有實際 source path 與可編譯使用例，特別涵蓋 Dedekind cuts、metric completion、Riemann–Stieltjes integral、ODE、Fourier／Gamma、differential forms／Stokes 及 `Lp`。證據：`docs/rudin/mathlib-coverage.md` 的來源對照與 `Support/ApiExamples.lean` 已編譯、納入根 imports 及全專案公理檢查；不宣稱已逐題完成 API 選型。
- [x] 建立第 6 章積分表示法的可編譯 prototype；驗收：明確說明表示法如何涵蓋 Rudin 的 monotone integrator、discontinuities 與 endpoint conventions，完成一個等價性或適用條件下的橋接結果。證據：literal weak-partition Darboux sums、完整 Darboux／tagged equivalence、raw interval-monotone integrator 的 continuous-integrand existence，以及 `StieltjesFunction ℝ` 下的 continuous real-integrand measure bridge 均已編譯並獨立覆核，涵蓋 singleton、zero mass、repeated nodes 與左右端點 atom 慣例。一般 raw normalization／endpoint correction 與 discontinuous integrand bridge 仍未完成，既有反例繼續禁止無條件替換。
- [ ] 建立第 10 章所需基礎設施的可編譯 prototype；驗收：按實際習題需求檢查 differential forms、pullback、exterior derivative、chains、orientation 與 integration 的表示法，完成一個非平凡運算及一個實際所需的 integration／boundary identity，列出尚缺定理與相依順序。不預設 Mathlib 已具備整套 Stokes theory。Progress: actual `extDeriv` computations and segment/rectangle boundary identities compile. The orientation quotient, fixed degrees, affine faces and parameterized-square boundaries now pass independent review. The new path-only integration/source-Darboux comparison also passes review and project checks. General smooth simplex chains, higher-dimensional simplex integration and their Rudin comparisons remain open.
- [x] 補齊第 6 章 partitions 的 common refinement、sum bounds 與 Darboux／tagged equivalence；驗收：有不依賴待證結論的 Lean 定理，並以定值及點支撐 integrand 檢查表示法。證據：`StieltjesRefinement.lean` 的 exact node-union refinement、sum／refinement bounds 與 `StieltjesEquivalence.lean` 的 actual predicate iff 通過獨立覆核及全專案檢查；regression 包含定值、pointSpike、singleton、zero increment、repeated nodes 及 extrema 不取得的例子。
- [x] 建立第 6 章非定值 integrand 的積分橋接及必要 jump／endpoint 條件；驗收：至少覆蓋 continuous integrands 並形式化比較，既有端點反例仍成立，不放寬信任條件。證據：`StieltjesMeasureBridge.continuous_bridge` 在 explicit right-continuous `StieltjesFunction ℝ`、`a ≤ b`、`ContinuousOn f (Icc a b)` 下證明 actual Darboux integral 與 `(a,b]` measure integral 相同；非定值、terminal jump、initial atom 排除、singleton／zero mass 測試通過。獨立覆核 final SHA256 `2e59487e32734474713a6d4e7f8f43e1b62d0e84010c5134d6a18271a1f6f37a`；不宣稱任意 raw integrator 的 measure comparison。
- [ ] 建立第 10 章所需的 signed affine／parameterized chains 與 face maps；驗收：證明 `∂² = 0`、面抵消與 multiplicity，並對照第 16–19、32 題的義務。Progress: `OrderedChains.lean` retains the raw augmented model. `OrientedChains.lean` adds a proved boundary-stable orientation quotient, fixed degrees, affine realization and face maps, square/cube signs and actual parameterized-square/Möbius multiplicities. `OrientedChainChecks.lean` proves nontriviality and coordinate-insertion signs. General smooth simplex chains, geometric coverage/orientation, square-triangulation comparison and integration remain open. Raw reversed edges are not identified without the quotient.
- [ ] 建立第 10 章 forms 的 pullback／simplex integration 與 Rudin 積分的比較；驗收：在所需規則性與方向條件下證明比較和 boundary identities，不用已假設的 Stokes identity 證明自身。 Progress: `PathIntegration.lean` proves the path-only coefficient, quotient integral, actual exterior-derivative boundary identity and continuous-coefficient Darboux bridge. Higher-dimensional simplexes and general reparameterization remain open.
- [x] 完成代表題 `R01E01`、`R02E02`、`R03E24`、`R06E01`、`R09E01`、`R11E01` 的全部義務；驗收：每題語義覆核、編譯、公理檢查及清單對照均通過。證據：六題共 15 個義務均為 `verified`；獨立覆核確認實際 Cauchy-sequence quotient 與完備化橋接，以及實際 Darboux 積分。R06E01 首輪發現嚴格 partition／零長區間漏列，已修正成 weak partition 與 `a ≤ b`，第二輪獨立覆核、singleton／endpoint 測試及整合檢查均通過。
- [x] 根據 prototype 與代表題更新此計畫、共用表示法及章別工作量；驗收：重大缺口拆成可執行任務，未解決的正確性問題明確阻塞受影響題目，時程估計只依實測分類，不宣稱各題成本相同。證據：更新 `formalization.md`、`mathlib-coverage.md` 與 P3 相依任務，並完成來源契約分類。工作量分為現成 lemma 題組、需明確構造／比較定理的題組、Darboux／measure 基礎設施、oriented parameterized chain／integration 基礎設施；依第 1 章與兩類 prototype 的實作證據分類，不給未量測的全書工期。

### P4 — 驗證已知原題問題

- [x] 完成 `R01E19` 的退化情況反例、非退化版本及完整分類；驗收：Lean 驗證來源問題與修正後結果，`errata.md` 記錄原條件、修正及對應 declaration。證據：4 個義務通過獨立覆核與整合檢查；反例排除所有可能的正半徑球面，不只檢查原公式。
- [x] 完成 `R11E18` 的零函數反例與完整 Schwarz equality 條件；驗收：Lean 驗證反例與包含退化情況的正確版本，不以額外非零假設掩蓋來源問題。證據：4 個義務通過獨立覆核與整合檢查；已證明 complex L2／原積分橋接、完整零函數分支與有限 Dirac measure 反例。

### P5 — 依章完成全部題目

以下每項均只處理尚未完成的題目；P3、P4 的成果不重複計數。章順序是預設順序，實際以清單中的題目相依關係為準。每批以 3–5 題為起點，大型構造題單獨處理。

- [x] 完成第 1 章 1–20 題；驗收：全部子義務通過本節的逐批門檻，包含複數根、等號條件、維度分類與修改 cuts 定義的構造。證據：20／20 題、55／55 個義務已完成單檔編譯、獨立來源／型別覆核與第二批整合公理檢查；19 題按原敘述證明，R01E19 以反例與修正版完成。根 imports 已涵蓋所有 20 題。
- [x] 完成第 2 章 1–30 題；驗收：全部子義務通過逐批門檻，並明確區分有限、至多可數與可數無限。 Evidence: 30/30 exercises and 71/71 obligations passed independent source/type review, compilation, project and isolated-source checks. R02E29 retains the bounded-segment obstruction and explicit extended-interval correction; R02E28 keeps the source countably-infinite convention. Actual decimal4/7 expansions, irrational perfect-set construction and the required nested-ball Baire proof are included.
- [x] 完成第 3 章 1–25 題；驗收：全部子義務通過逐批門檻，包含完備化構造、稠密嵌入與相關識別結果。 Evidence: 25/25 resolutions and 89/89 obligations pass independent source/type review, compilation, full project and isolated-source checks. Includes ordinary conditional series, full Tauberian outline, vector-series extensions, Newton classifications, literal Cantor digits and the actual quotient completion of the rationals. R03E14's added source obstruction is retained.
- [x] 完成第 4 章 1–26 題；驗收：全部子義務通過逐批門檻，逆命題及移除假設的問題均有判定與所需反例。 Evidence: all 26 resolutions and 74 obligations pass independent source/type review, full project checks and isolated-source rebuild. R04E05 also covers the arbitrary metric domain stated in the source; R04E26's optional forward helpers add no source obligations.
- [x] 完成第 5 章 1–29 題；驗收：全部子義務通過逐批門檻，端點導數、ODE uniqueness 與指定初始條件語義一致。 Evidence: all 29 resolutions and 84 obligations pass independent source/type/body reviews, default project checks and isolated-source rebuilding. Actual one-sided derivative chains, every initial datum, complete ODE waiting-time classification, sharp threshold equality cases, and both explicit source corrections are retained.
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

- [x] 11 章所有來源題目與子義務均完成核對，正式總數有來源依據。Evidence: `exercises.json` and `source.md` record 287 exercises and 849 obligations: the initial 839, eight source-clarification checks, R03E14's zero-bound obstruction, and R06E02's explicit comparison. Changes are justified in `source-clarifications.md`.這項來源盤點不表示題意問題全部解決或 Lean 證明全部完成。
- [ ] 全部義務均為 `verified`，沒有 `todo`、`in_progress`、`blocked` 或未完成的構造／追問。
- [ ] 原題不成立的情況有 Lean 反例與標示清楚的正確替代結果；沒有將錯誤原命題計為已證明。
- [ ] 全部目前交付模組納入預設建置；不存在以未匯入檔案隱藏未完成證明的情況。 Sixth-batch checks pass for all 135 integrated exercise modules, including the unfinished R06E02. Kept open while new Chapter 6 sources are developed and await root integration.
- [ ] 全部目前交付與 Support declarations 通過公理檢查，無佔位證明、自訂公理或未授權的信任擴充。 Sixth-batch project and isolated-copy audits pass for 2241 local declarations and 504 references. Kept open for new Chapter 6 sources; no unsafe, partial or nonstandard-axiom exception is permitted.
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
