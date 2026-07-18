import VersoSlides
import Theme
import Slides

open VersoSlides

def main : IO UInt32 :=
  slidesMain
    (config := {
      theme := .custom leanaideTheme
      extraCss := #[leanaideOverrides]
      transition := "fade"
      slideNumber := true
      width := 1280
      height := 800
      margin := 0.06
    })
    (doc := %doc Slides)
