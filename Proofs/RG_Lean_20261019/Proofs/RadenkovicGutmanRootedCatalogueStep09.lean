/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block000
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block001
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block002
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block003
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block004
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block005
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block006
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block007
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block008
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block009
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block010
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block011
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block012
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block013
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block014
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block015
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block016
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block017
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block018
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block019
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block020
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block021
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block022
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block023
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block024
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block025
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block026
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block027
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block028
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block029
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block030
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block031
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block032
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block033
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block034
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block035
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block036
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block037
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block038
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block039
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block040
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block041
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block042
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block043
import Proofs.RadenkovicGutmanRootedCatalogueStep09Block044
namespace Gebendorfer.RadenkovicGutman.RootedCatalogueData
open RootedTreeEnumeration CanonicalTreeCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem step9 : ∀ i : Fin level9.length, ∀ v : Vertices 9,
    ∃ j : Fin level10.length,
      ∃ e : graph (n := 10) (level9.get i,v) ≃g graph (level10.get j),
        e (root 10)=root 10 := by
  intro i v
  have hi := i.isLt
  change i.val < 719 at hi
  by_cases h0 : i.val < 16
  · exact range_sound 9 level9 level10 0 16 (by decide) witnesses9b000 checked9b000
      ⟨i.val-0,by omega⟩ v i (by omega)
  ·
    by_cases h1 : i.val < 32
    · exact range_sound 9 level9 level10 16 16 (by decide) witnesses9b001 checked9b001
        ⟨i.val-16,by omega⟩ v i (by omega)
    ·
      by_cases h2 : i.val < 48
      · exact range_sound 9 level9 level10 32 16 (by decide) witnesses9b002 checked9b002
          ⟨i.val-32,by omega⟩ v i (by omega)
      ·
        by_cases h3 : i.val < 64
        · exact range_sound 9 level9 level10 48 16 (by decide) witnesses9b003 checked9b003
            ⟨i.val-48,by omega⟩ v i (by omega)
        ·
          by_cases h4 : i.val < 80
          · exact range_sound 9 level9 level10 64 16 (by decide) witnesses9b004 checked9b004
              ⟨i.val-64,by omega⟩ v i (by omega)
          ·
            by_cases h5 : i.val < 96
            · exact range_sound 9 level9 level10 80 16 (by decide) witnesses9b005 checked9b005
                ⟨i.val-80,by omega⟩ v i (by omega)
            ·
              by_cases h6 : i.val < 112
              · exact range_sound 9 level9 level10 96 16 (by decide) witnesses9b006 checked9b006
                  ⟨i.val-96,by omega⟩ v i (by omega)
              ·
                by_cases h7 : i.val < 128
                · exact range_sound 9 level9 level10 112 16 (by decide) witnesses9b007 checked9b007
                    ⟨i.val-112,by omega⟩ v i (by omega)
                ·
                  by_cases h8 : i.val < 144
                  · exact range_sound 9 level9 level10 128 16 (by decide) witnesses9b008 checked9b008
                      ⟨i.val-128,by omega⟩ v i (by omega)
                  ·
                    by_cases h9 : i.val < 160
                    · exact range_sound 9 level9 level10 144 16 (by decide) witnesses9b009 checked9b009
                        ⟨i.val-144,by omega⟩ v i (by omega)
                    ·
                      by_cases h10 : i.val < 176
                      · exact range_sound 9 level9 level10 160 16 (by decide) witnesses9b010 checked9b010
                          ⟨i.val-160,by omega⟩ v i (by omega)
                      ·
                        by_cases h11 : i.val < 192
                        · exact range_sound 9 level9 level10 176 16 (by decide) witnesses9b011 checked9b011
                            ⟨i.val-176,by omega⟩ v i (by omega)
                        ·
                          by_cases h12 : i.val < 208
                          · exact range_sound 9 level9 level10 192 16 (by decide) witnesses9b012 checked9b012
                              ⟨i.val-192,by omega⟩ v i (by omega)
                          ·
                            by_cases h13 : i.val < 224
                            · exact range_sound 9 level9 level10 208 16 (by decide) witnesses9b013 checked9b013
                                ⟨i.val-208,by omega⟩ v i (by omega)
                            ·
                              by_cases h14 : i.val < 240
                              · exact range_sound 9 level9 level10 224 16 (by decide) witnesses9b014 checked9b014
                                  ⟨i.val-224,by omega⟩ v i (by omega)
                              ·
                                by_cases h15 : i.val < 256
                                · exact range_sound 9 level9 level10 240 16 (by decide) witnesses9b015 checked9b015
                                    ⟨i.val-240,by omega⟩ v i (by omega)
                                ·
                                  by_cases h16 : i.val < 272
                                  · exact range_sound 9 level9 level10 256 16 (by decide) witnesses9b016 checked9b016
                                      ⟨i.val-256,by omega⟩ v i (by omega)
                                  ·
                                    by_cases h17 : i.val < 288
                                    · exact range_sound 9 level9 level10 272 16 (by decide) witnesses9b017 checked9b017
                                        ⟨i.val-272,by omega⟩ v i (by omega)
                                    ·
                                      by_cases h18 : i.val < 304
                                      · exact range_sound 9 level9 level10 288 16 (by decide) witnesses9b018 checked9b018
                                          ⟨i.val-288,by omega⟩ v i (by omega)
                                      ·
                                        by_cases h19 : i.val < 320
                                        · exact range_sound 9 level9 level10 304 16 (by decide) witnesses9b019 checked9b019
                                            ⟨i.val-304,by omega⟩ v i (by omega)
                                        ·
                                          by_cases h20 : i.val < 336
                                          · exact range_sound 9 level9 level10 320 16 (by decide) witnesses9b020 checked9b020
                                              ⟨i.val-320,by omega⟩ v i (by omega)
                                          ·
                                            by_cases h21 : i.val < 352
                                            · exact range_sound 9 level9 level10 336 16 (by decide) witnesses9b021 checked9b021
                                                ⟨i.val-336,by omega⟩ v i (by omega)
                                            ·
                                              by_cases h22 : i.val < 368
                                              · exact range_sound 9 level9 level10 352 16 (by decide) witnesses9b022 checked9b022
                                                  ⟨i.val-352,by omega⟩ v i (by omega)
                                              ·
                                                by_cases h23 : i.val < 384
                                                · exact range_sound 9 level9 level10 368 16 (by decide) witnesses9b023 checked9b023
                                                    ⟨i.val-368,by omega⟩ v i (by omega)
                                                ·
                                                  by_cases h24 : i.val < 400
                                                  · exact range_sound 9 level9 level10 384 16 (by decide) witnesses9b024 checked9b024
                                                      ⟨i.val-384,by omega⟩ v i (by omega)
                                                  ·
                                                    by_cases h25 : i.val < 416
                                                    · exact range_sound 9 level9 level10 400 16 (by decide) witnesses9b025 checked9b025
                                                        ⟨i.val-400,by omega⟩ v i (by omega)
                                                    ·
                                                      by_cases h26 : i.val < 432
                                                      · exact range_sound 9 level9 level10 416 16 (by decide) witnesses9b026 checked9b026
                                                          ⟨i.val-416,by omega⟩ v i (by omega)
                                                      ·
                                                        by_cases h27 : i.val < 448
                                                        · exact range_sound 9 level9 level10 432 16 (by decide) witnesses9b027 checked9b027
                                                            ⟨i.val-432,by omega⟩ v i (by omega)
                                                        ·
                                                          by_cases h28 : i.val < 464
                                                          · exact range_sound 9 level9 level10 448 16 (by decide) witnesses9b028 checked9b028
                                                              ⟨i.val-448,by omega⟩ v i (by omega)
                                                          ·
                                                            by_cases h29 : i.val < 480
                                                            · exact range_sound 9 level9 level10 464 16 (by decide) witnesses9b029 checked9b029
                                                                ⟨i.val-464,by omega⟩ v i (by omega)
                                                            ·
                                                              by_cases h30 : i.val < 496
                                                              · exact range_sound 9 level9 level10 480 16 (by decide) witnesses9b030 checked9b030
                                                                  ⟨i.val-480,by omega⟩ v i (by omega)
                                                              ·
                                                                by_cases h31 : i.val < 512
                                                                · exact range_sound 9 level9 level10 496 16 (by decide) witnesses9b031 checked9b031
                                                                    ⟨i.val-496,by omega⟩ v i (by omega)
                                                                ·
                                                                  by_cases h32 : i.val < 528
                                                                  · exact range_sound 9 level9 level10 512 16 (by decide) witnesses9b032 checked9b032
                                                                      ⟨i.val-512,by omega⟩ v i (by omega)
                                                                  ·
                                                                    by_cases h33 : i.val < 544
                                                                    · exact range_sound 9 level9 level10 528 16 (by decide) witnesses9b033 checked9b033
                                                                        ⟨i.val-528,by omega⟩ v i (by omega)
                                                                    ·
                                                                      by_cases h34 : i.val < 560
                                                                      · exact range_sound 9 level9 level10 544 16 (by decide) witnesses9b034 checked9b034
                                                                          ⟨i.val-544,by omega⟩ v i (by omega)
                                                                      ·
                                                                        by_cases h35 : i.val < 576
                                                                        · exact range_sound 9 level9 level10 560 16 (by decide) witnesses9b035 checked9b035
                                                                            ⟨i.val-560,by omega⟩ v i (by omega)
                                                                        ·
                                                                          by_cases h36 : i.val < 592
                                                                          · exact range_sound 9 level9 level10 576 16 (by decide) witnesses9b036 checked9b036
                                                                              ⟨i.val-576,by omega⟩ v i (by omega)
                                                                          ·
                                                                            by_cases h37 : i.val < 608
                                                                            · exact range_sound 9 level9 level10 592 16 (by decide) witnesses9b037 checked9b037
                                                                                ⟨i.val-592,by omega⟩ v i (by omega)
                                                                            ·
                                                                              by_cases h38 : i.val < 624
                                                                              · exact range_sound 9 level9 level10 608 16 (by decide) witnesses9b038 checked9b038
                                                                                  ⟨i.val-608,by omega⟩ v i (by omega)
                                                                              ·
                                                                                by_cases h39 : i.val < 640
                                                                                · exact range_sound 9 level9 level10 624 16 (by decide) witnesses9b039 checked9b039
                                                                                    ⟨i.val-624,by omega⟩ v i (by omega)
                                                                                ·
                                                                                  by_cases h40 : i.val < 656
                                                                                  · exact range_sound 9 level9 level10 640 16 (by decide) witnesses9b040 checked9b040
                                                                                      ⟨i.val-640,by omega⟩ v i (by omega)
                                                                                  ·
                                                                                    by_cases h41 : i.val < 672
                                                                                    · exact range_sound 9 level9 level10 656 16 (by decide) witnesses9b041 checked9b041
                                                                                        ⟨i.val-656,by omega⟩ v i (by omega)
                                                                                    ·
                                                                                      by_cases h42 : i.val < 688
                                                                                      · exact range_sound 9 level9 level10 672 16 (by decide) witnesses9b042 checked9b042
                                                                                          ⟨i.val-672,by omega⟩ v i (by omega)
                                                                                      ·
                                                                                        by_cases h43 : i.val < 704
                                                                                        · exact range_sound 9 level9 level10 688 16 (by decide) witnesses9b043 checked9b043
                                                                                            ⟨i.val-688,by omega⟩ v i (by omega)
                                                                                        ·
                                                                                          exact range_sound 9 level9 level10 704 15 (by decide) witnesses9b044 checked9b044
                                                                                              ⟨i.val-704,by omega⟩ v i (by omega)
#print axioms step9
end Gebendorfer.RadenkovicGutman.RootedCatalogueData
