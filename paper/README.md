# 論文執筆環境

`main.tex` を入口とし，各章の原稿を `sections/` に分割して管理する．
`tech-sample-css.tex` はCSS原稿フォーマットの正本として扱い，文書クラス，パッケージ，マクロ，和英メタデータ環境の順序を `main.tex` でも維持する．`tech-sample-css.pdf` は出力見本である．いずれも論文本文のビルド対象ではない．

## 構成

- `main.tex`: 題目，著者情報，概要，章ファイルの読み込み
- `sections/01_introduction.tex`: はじめに
- `sections/02_related_work.tex`: 関連研究
- `sections/03_method.tex`: 問題設定と提案手法
- `sections/04_implementation.tex`: 実装
- `sections/05_evaluation.tex`: 評価
- `sections/06_conclusion.tex`: おわりに
- `figures/`: 図のソースおよび論文から参照する画像
- `css.cls`, `ipsj.cls`, `ipsjtech.sty`: CSS/IPSJスタイル
- `tech-sample-css.*`: テンプレートの参照資料

## ビルド

Dockerを利用する場合は，`paper` ディレクトリで次を実行する．

```sh
make build
```

`make build` は最初に `main.tex` のテンプレート形式を検査する．形式だけを確認する場合は `make check-template` を実行する．生成物は `build/main.pdf` に置かれる．同梱のCSS/IPSJクラスに合わせ，`.latexmkrc` でpLaTeXとdvipdfmxを使用する．日本語表示が閲覧環境に依存しないよう，DockerイメージではIPAexフォントを埋め込む．中間ファイルを削除する場合は `make clean` を実行する．
Dockerイメージには，生成PDFのページ情報確認と画像化に使用できるPopplerも含めている．

## 執筆前に確定する項目

1. 正式な和文・英文題目，著者名，所属，代表メールアドレス
2. 投稿先と原稿種別，ページ数，匿名化，研究倫理に関する要件
3. 本文中でいう「章」をCSS原稿の `section` として扱うか，学位論文用クラスへ変更するか
4. 関連研究の調査範囲と，テンプレートの `thebibliography` 形式で記載する引用文献
5. EQBENCHの版，対象ペア，ビルド条件，実行環境，タイムアウト値
6. EQ / NOT\_EQ / UNKNOWN / TIMEOUT / ERRORの集計元となる確定成果物
7. UNKNOWN理由の論文上の分類と，実装が出力する正規reason IDとの対応
8. 図表一覧（全体構成，処理フロー，判定基準，評価結果）

`TODO(...)` コメントは未確定事項を表す．実験結果や既存研究との差分は，根拠が確定するまで数値や優位性を補わない．
