/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block000
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block001
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block002
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block003
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block004
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block005
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block006
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block007
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block008
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block009
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block010
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block011
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block012
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block013
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block014
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block015
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block016
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block017
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block018
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block019
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block020
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block021
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block022
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block023
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block024
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block025
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block026
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block027
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block028
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block029
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block030
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block031
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block032
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block033
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block034
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoreCoverage08Block035
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered8 : decide (∀ i : Fin (RootedCatalogueData.catalogue 8).length,
    ∀ p q : Fin 13, eligible 8 i.val p.val q.val=true →
      (⟨8,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 286 at hi
  by_cases h0 : i.val < 8
  · exact CoreCoverage.range_sound 8 0 8 CoreCoverage.checked8b000 i.val p q (by omega) (by omega) he
  ·
    by_cases h1 : i.val < 16
    · exact CoreCoverage.range_sound 8 8 8 CoreCoverage.checked8b001 i.val p q (by omega) (by omega) he
    ·
      by_cases h2 : i.val < 24
      · exact CoreCoverage.range_sound 8 16 8 CoreCoverage.checked8b002 i.val p q (by omega) (by omega) he
      ·
        by_cases h3 : i.val < 32
        · exact CoreCoverage.range_sound 8 24 8 CoreCoverage.checked8b003 i.val p q (by omega) (by omega) he
        ·
          by_cases h4 : i.val < 40
          · exact CoreCoverage.range_sound 8 32 8 CoreCoverage.checked8b004 i.val p q (by omega) (by omega) he
          ·
            by_cases h5 : i.val < 48
            · exact CoreCoverage.range_sound 8 40 8 CoreCoverage.checked8b005 i.val p q (by omega) (by omega) he
            ·
              by_cases h6 : i.val < 56
              · exact CoreCoverage.range_sound 8 48 8 CoreCoverage.checked8b006 i.val p q (by omega) (by omega) he
              ·
                by_cases h7 : i.val < 64
                · exact CoreCoverage.range_sound 8 56 8 CoreCoverage.checked8b007 i.val p q (by omega) (by omega) he
                ·
                  by_cases h8 : i.val < 72
                  · exact CoreCoverage.range_sound 8 64 8 CoreCoverage.checked8b008 i.val p q (by omega) (by omega) he
                  ·
                    by_cases h9 : i.val < 80
                    · exact CoreCoverage.range_sound 8 72 8 CoreCoverage.checked8b009 i.val p q (by omega) (by omega) he
                    ·
                      by_cases h10 : i.val < 88
                      · exact CoreCoverage.range_sound 8 80 8 CoreCoverage.checked8b010 i.val p q (by omega) (by omega) he
                      ·
                        by_cases h11 : i.val < 96
                        · exact CoreCoverage.range_sound 8 88 8 CoreCoverage.checked8b011 i.val p q (by omega) (by omega) he
                        ·
                          by_cases h12 : i.val < 104
                          · exact CoreCoverage.range_sound 8 96 8 CoreCoverage.checked8b012 i.val p q (by omega) (by omega) he
                          ·
                            by_cases h13 : i.val < 112
                            · exact CoreCoverage.range_sound 8 104 8 CoreCoverage.checked8b013 i.val p q (by omega) (by omega) he
                            ·
                              by_cases h14 : i.val < 120
                              · exact CoreCoverage.range_sound 8 112 8 CoreCoverage.checked8b014 i.val p q (by omega) (by omega) he
                              ·
                                by_cases h15 : i.val < 128
                                · exact CoreCoverage.range_sound 8 120 8 CoreCoverage.checked8b015 i.val p q (by omega) (by omega) he
                                ·
                                  by_cases h16 : i.val < 136
                                  · exact CoreCoverage.range_sound 8 128 8 CoreCoverage.checked8b016 i.val p q (by omega) (by omega) he
                                  ·
                                    by_cases h17 : i.val < 144
                                    · exact CoreCoverage.range_sound 8 136 8 CoreCoverage.checked8b017 i.val p q (by omega) (by omega) he
                                    ·
                                      by_cases h18 : i.val < 152
                                      · exact CoreCoverage.range_sound 8 144 8 CoreCoverage.checked8b018 i.val p q (by omega) (by omega) he
                                      ·
                                        by_cases h19 : i.val < 160
                                        · exact CoreCoverage.range_sound 8 152 8 CoreCoverage.checked8b019 i.val p q (by omega) (by omega) he
                                        ·
                                          by_cases h20 : i.val < 168
                                          · exact CoreCoverage.range_sound 8 160 8 CoreCoverage.checked8b020 i.val p q (by omega) (by omega) he
                                          ·
                                            by_cases h21 : i.val < 176
                                            · exact CoreCoverage.range_sound 8 168 8 CoreCoverage.checked8b021 i.val p q (by omega) (by omega) he
                                            ·
                                              by_cases h22 : i.val < 184
                                              · exact CoreCoverage.range_sound 8 176 8 CoreCoverage.checked8b022 i.val p q (by omega) (by omega) he
                                              ·
                                                by_cases h23 : i.val < 192
                                                · exact CoreCoverage.range_sound 8 184 8 CoreCoverage.checked8b023 i.val p q (by omega) (by omega) he
                                                ·
                                                  by_cases h24 : i.val < 200
                                                  · exact CoreCoverage.range_sound 8 192 8 CoreCoverage.checked8b024 i.val p q (by omega) (by omega) he
                                                  ·
                                                    by_cases h25 : i.val < 208
                                                    · exact CoreCoverage.range_sound 8 200 8 CoreCoverage.checked8b025 i.val p q (by omega) (by omega) he
                                                    ·
                                                      by_cases h26 : i.val < 216
                                                      · exact CoreCoverage.range_sound 8 208 8 CoreCoverage.checked8b026 i.val p q (by omega) (by omega) he
                                                      ·
                                                        by_cases h27 : i.val < 224
                                                        · exact CoreCoverage.range_sound 8 216 8 CoreCoverage.checked8b027 i.val p q (by omega) (by omega) he
                                                        ·
                                                          by_cases h28 : i.val < 232
                                                          · exact CoreCoverage.range_sound 8 224 8 CoreCoverage.checked8b028 i.val p q (by omega) (by omega) he
                                                          ·
                                                            by_cases h29 : i.val < 240
                                                            · exact CoreCoverage.range_sound 8 232 8 CoreCoverage.checked8b029 i.val p q (by omega) (by omega) he
                                                            ·
                                                              by_cases h30 : i.val < 248
                                                              · exact CoreCoverage.range_sound 8 240 8 CoreCoverage.checked8b030 i.val p q (by omega) (by omega) he
                                                              ·
                                                                by_cases h31 : i.val < 256
                                                                · exact CoreCoverage.range_sound 8 248 8 CoreCoverage.checked8b031 i.val p q (by omega) (by omega) he
                                                                ·
                                                                  by_cases h32 : i.val < 264
                                                                  · exact CoreCoverage.range_sound 8 256 8 CoreCoverage.checked8b032 i.val p q (by omega) (by omega) he
                                                                  ·
                                                                    by_cases h33 : i.val < 272
                                                                    · exact CoreCoverage.range_sound 8 264 8 CoreCoverage.checked8b033 i.val p q (by omega) (by omega) he
                                                                    ·
                                                                      by_cases h34 : i.val < 280
                                                                      · exact CoreCoverage.range_sound 8 272 8 CoreCoverage.checked8b034 i.val p q (by omega) (by omega) he
                                                                      ·
                                                                        exact CoreCoverage.range_sound 8 280 6 CoreCoverage.checked8b035 i.val p q (by omega) (by omega) he
#print axioms covered8
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
