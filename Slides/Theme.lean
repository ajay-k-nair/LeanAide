import VersoSlides
import VersoUtil.BinFiles

open VersoSlides
open Verso.BinFiles

/-- LeanAide's custom `reveal.js` theme: dark, spacious, built around
Poppins / Inter / JetBrains Mono with a cyan-to-violet accent gradient,
all bundled offline. -/
def leanaideTheme : CustomTheme where
  stylesheet := { filename := "theme.css", contents := ⟨include_str "assets/theme.css"⟩ }
  assets := #[
    { filename := "fonts/PoppinsBold.ttf", contents := include_bin "assets/fonts/Poppins-Bold.ttf" },
    { filename := "fonts/PoppinsExtraBold.ttf", contents := include_bin "assets/fonts/Poppins-ExtraBold.ttf" },
    { filename := "fonts/PoppinsSemiBold.ttf", contents := include_bin "assets/fonts/Poppins-SemiBold.ttf" },
    { filename := "fonts/Inter.ttf", contents := include_bin "assets/fonts/Inter.ttf" },
    { filename := "fonts/JetBrainsMono.ttf", contents := include_bin "assets/fonts/JetBrainsMono.ttf" }
  ]
  highlightTheme := .atomOneDark

/-- Targeted overrides for VersoSlides' own component stylesheets (code
panels, tables); see `assets/overrides.css` for why these need `extraCss`
rather than living in the theme stylesheet itself. -/
def leanaideOverrides : CssFile where
  filename := "leanaide-overrides.css"
  contents := ⟨include_str "assets/overrides.css"⟩
