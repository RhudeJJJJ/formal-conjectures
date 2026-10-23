/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData

namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteListAssembly
open SmallGeFourKeys DegreeTwoThreeFiniteKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem of_batches (Q : SmallGeFourKeys.Key → Prop)
    (h000 : ∀ k ∈ keys000, Q k)
    (h001 : ∀ k ∈ keys001, Q k)
    (h002 : ∀ k ∈ keys002, Q k)
    (h003 : ∀ k ∈ keys003, Q k)
    (h004 : ∀ k ∈ keys004, Q k)
    (h005 : ∀ k ∈ keys005, Q k)
    (h006 : ∀ k ∈ keys006, Q k)
    (h007 : ∀ k ∈ keys007, Q k)
    (h008 : ∀ k ∈ keys008, Q k)
    (h009 : ∀ k ∈ keys009, Q k)
    (h010 : ∀ k ∈ keys010, Q k)
    (h011 : ∀ k ∈ keys011, Q k)
    (h012 : ∀ k ∈ keys012, Q k)
    (h013 : ∀ k ∈ keys013, Q k)
    (h014 : ∀ k ∈ keys014, Q k)
    (h015 : ∀ k ∈ keys015, Q k)
    (h016 : ∀ k ∈ keys016, Q k)
    (h017 : ∀ k ∈ keys017, Q k)
    (h018 : ∀ k ∈ keys018, Q k)
    (h019 : ∀ k ∈ keys019, Q k)
    (h020 : ∀ k ∈ keys020, Q k)
    (h021 : ∀ k ∈ keys021, Q k)
    (h022 : ∀ k ∈ keys022, Q k)
    (h023 : ∀ k ∈ keys023, Q k)
    (h024 : ∀ k ∈ keys024, Q k)
    (h025 : ∀ k ∈ keys025, Q k)
    (h026 : ∀ k ∈ keys026, Q k)
    (h027 : ∀ k ∈ keys027, Q k)
    (h028 : ∀ k ∈ keys028, Q k)
    (h029 : ∀ k ∈ keys029, Q k)
    (h030 : ∀ k ∈ keys030, Q k)
    (h031 : ∀ k ∈ keys031, Q k)
    (h032 : ∀ k ∈ keys032, Q k)
    (h033 : ∀ k ∈ keys033, Q k)
    (h034 : ∀ k ∈ keys034, Q k)
    (h035 : ∀ k ∈ keys035, Q k)
    (h036 : ∀ k ∈ keys036, Q k)
    (h037 : ∀ k ∈ keys037, Q k)
    (h038 : ∀ k ∈ keys038, Q k)
    (h039 : ∀ k ∈ keys039, Q k)
    (h040 : ∀ k ∈ keys040, Q k)
    (h041 : ∀ k ∈ keys041, Q k)
    (h042 : ∀ k ∈ keys042, Q k)
    (h043 : ∀ k ∈ keys043, Q k)
    (h044 : ∀ k ∈ keys044, Q k)
    (h045 : ∀ k ∈ keys045, Q k)
    (h046 : ∀ k ∈ keys046, Q k)
    (h047 : ∀ k ∈ keys047, Q k)
    (h048 : ∀ k ∈ keys048, Q k)
    (h049 : ∀ k ∈ keys049, Q k)
    (h050 : ∀ k ∈ keys050, Q k)
    (h051 : ∀ k ∈ keys051, Q k)
    (h052 : ∀ k ∈ keys052, Q k)
    (h053 : ∀ k ∈ keys053, Q k)
    (h054 : ∀ k ∈ keys054, Q k)
    (h055 : ∀ k ∈ keys055, Q k)
    (h056 : ∀ k ∈ keys056, Q k)
    (h057 : ∀ k ∈ keys057, Q k)
    (h058 : ∀ k ∈ keys058, Q k)
    (h059 : ∀ k ∈ keys059, Q k)
    (h060 : ∀ k ∈ keys060, Q k)
    (h061 : ∀ k ∈ keys061, Q k)
    (h062 : ∀ k ∈ keys062, Q k)
    (h063 : ∀ k ∈ keys063, Q k)
    (h064 : ∀ k ∈ keys064, Q k)
    (h065 : ∀ k ∈ keys065, Q k)
    (h066 : ∀ k ∈ keys066, Q k)
    (h067 : ∀ k ∈ keys067, Q k)
    (h068 : ∀ k ∈ keys068, Q k)
    (h069 : ∀ k ∈ keys069, Q k)
    (h070 : ∀ k ∈ keys070, Q k)
    (h071 : ∀ k ∈ keys071, Q k)
    (h072 : ∀ k ∈ keys072, Q k)
    (h073 : ∀ k ∈ keys073, Q k)
    (h074 : ∀ k ∈ keys074, Q k)
    (h075 : ∀ k ∈ keys075, Q k)
    (h076 : ∀ k ∈ keys076, Q k)
    (h077 : ∀ k ∈ keys077, Q k)
    (h078 : ∀ k ∈ keys078, Q k)
    (h079 : ∀ k ∈ keys079, Q k)
    (h080 : ∀ k ∈ keys080, Q k)
    (h081 : ∀ k ∈ keys081, Q k)
    (h082 : ∀ k ∈ keys082, Q k)
    (h083 : ∀ k ∈ keys083, Q k)
    (h084 : ∀ k ∈ keys084, Q k)
    (h085 : ∀ k ∈ keys085, Q k)
    (h086 : ∀ k ∈ keys086, Q k)
    (h087 : ∀ k ∈ keys087, Q k)
    (h088 : ∀ k ∈ keys088, Q k)
    (h089 : ∀ k ∈ keys089, Q k)
    (h090 : ∀ k ∈ keys090, Q k)
    (h091 : ∀ k ∈ keys091, Q k)
    (h092 : ∀ k ∈ keys092, Q k)
    (h093 : ∀ k ∈ keys093, Q k)
    (h094 : ∀ k ∈ keys094, Q k)
    (h095 : ∀ k ∈ keys095, Q k)
    (h096 : ∀ k ∈ keys096, Q k)
    (h097 : ∀ k ∈ keys097, Q k)
    (h098 : ∀ k ∈ keys098, Q k)
    (h099 : ∀ k ∈ keys099, Q k)
    (h100 : ∀ k ∈ keys100, Q k)
    (h101 : ∀ k ∈ keys101, Q k)
    (h102 : ∀ k ∈ keys102, Q k)
    (h103 : ∀ k ∈ keys103, Q k)
    (h104 : ∀ k ∈ keys104, Q k)
    (h105 : ∀ k ∈ keys105, Q k)
    (h106 : ∀ k ∈ keys106, Q k)
    (h107 : ∀ k ∈ keys107, Q k)
    (h108 : ∀ k ∈ keys108, Q k)
    (h109 : ∀ k ∈ keys109, Q k)
    (h110 : ∀ k ∈ keys110, Q k)
    : ∀ k ∈ DegreeTwoThreeFiniteKeys.keys, Q k := by
  intro k hk
  have hk := (List.mem_append.mp hk).resolve_right (List.not_mem_nil k)
  rcases List.mem_append.mp hk with hk | h
  · rcases List.mem_append.mp hk with hk | h
    · rcases List.mem_append.mp hk with hk | h
      · rcases List.mem_append.mp hk with hk | h
        · rcases List.mem_append.mp hk with hk | h
          · rcases List.mem_append.mp hk with hk | h
            · rcases List.mem_append.mp hk with hk | h
              · rcases List.mem_append.mp hk with hk | h
                · rcases List.mem_append.mp hk with hk | h
                  · rcases List.mem_append.mp hk with hk | h
                    · rcases List.mem_append.mp hk with hk | h
                      · rcases List.mem_append.mp hk with hk | h
                        · rcases List.mem_append.mp hk with hk | h
                          · rcases List.mem_append.mp hk with hk | h
                            · rcases List.mem_append.mp hk with hk | h
                              · rcases List.mem_append.mp hk with hk | h
                                · rcases List.mem_append.mp hk with hk | h
                                  · rcases List.mem_append.mp hk with hk | h
                                    · rcases List.mem_append.mp hk with hk | h
                                      · rcases List.mem_append.mp hk with hk | h
                                        · rcases List.mem_append.mp hk with hk | h
                                          · rcases List.mem_append.mp hk with hk | h
                                            · rcases List.mem_append.mp hk with hk | h
                                              · rcases List.mem_append.mp hk with hk | h
                                                · rcases List.mem_append.mp hk with hk | h
                                                  · rcases List.mem_append.mp hk with hk | h
                                                    · rcases List.mem_append.mp hk with hk | h
                                                      · rcases List.mem_append.mp hk with hk | h
                                                        · rcases List.mem_append.mp hk with hk | h
                                                          · rcases List.mem_append.mp hk with hk | h
                                                            · rcases List.mem_append.mp hk with hk | h
                                                              · rcases List.mem_append.mp hk with hk | h
                                                                · rcases List.mem_append.mp hk with hk | h
                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                            · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                              · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                                · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                                  · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                                    · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                                      · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                                        · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                                          · rcases List.mem_append.mp hk with hk | h
                                                                                                                                                                                                                            · exact h000 k hk
                                                                                                                                                                                                                            · exact h001 k h
                                                                                                                                                                                                                          · exact h002 k h
                                                                                                                                                                                                                        · exact h003 k h
                                                                                                                                                                                                                      · exact h004 k h
                                                                                                                                                                                                                    · exact h005 k h
                                                                                                                                                                                                                  · exact h006 k h
                                                                                                                                                                                                                · exact h007 k h
                                                                                                                                                                                                              · exact h008 k h
                                                                                                                                                                                                            · exact h009 k h
                                                                                                                                                                                                          · exact h010 k h
                                                                                                                                                                                                        · exact h011 k h
                                                                                                                                                                                                      · exact h012 k h
                                                                                                                                                                                                    · exact h013 k h
                                                                                                                                                                                                  · exact h014 k h
                                                                                                                                                                                                · exact h015 k h
                                                                                                                                                                                              · exact h016 k h
                                                                                                                                                                                            · exact h017 k h
                                                                                                                                                                                          · exact h018 k h
                                                                                                                                                                                        · exact h019 k h
                                                                                                                                                                                      · exact h020 k h
                                                                                                                                                                                    · exact h021 k h
                                                                                                                                                                                  · exact h022 k h
                                                                                                                                                                                · exact h023 k h
                                                                                                                                                                              · exact h024 k h
                                                                                                                                                                            · exact h025 k h
                                                                                                                                                                          · exact h026 k h
                                                                                                                                                                        · exact h027 k h
                                                                                                                                                                      · exact h028 k h
                                                                                                                                                                    · exact h029 k h
                                                                                                                                                                  · exact h030 k h
                                                                                                                                                                · exact h031 k h
                                                                                                                                                              · exact h032 k h
                                                                                                                                                            · exact h033 k h
                                                                                                                                                          · exact h034 k h
                                                                                                                                                        · exact h035 k h
                                                                                                                                                      · exact h036 k h
                                                                                                                                                    · exact h037 k h
                                                                                                                                                  · exact h038 k h
                                                                                                                                                · exact h039 k h
                                                                                                                                              · exact h040 k h
                                                                                                                                            · exact h041 k h
                                                                                                                                          · exact h042 k h
                                                                                                                                        · exact h043 k h
                                                                                                                                      · exact h044 k h
                                                                                                                                    · exact h045 k h
                                                                                                                                  · exact h046 k h
                                                                                                                                · exact h047 k h
                                                                                                                              · exact h048 k h
                                                                                                                            · exact h049 k h
                                                                                                                          · exact h050 k h
                                                                                                                        · exact h051 k h
                                                                                                                      · exact h052 k h
                                                                                                                    · exact h053 k h
                                                                                                                  · exact h054 k h
                                                                                                                · exact h055 k h
                                                                                                              · exact h056 k h
                                                                                                            · exact h057 k h
                                                                                                          · exact h058 k h
                                                                                                        · exact h059 k h
                                                                                                      · exact h060 k h
                                                                                                    · exact h061 k h
                                                                                                  · exact h062 k h
                                                                                                · exact h063 k h
                                                                                              · exact h064 k h
                                                                                            · exact h065 k h
                                                                                          · exact h066 k h
                                                                                        · exact h067 k h
                                                                                      · exact h068 k h
                                                                                    · exact h069 k h
                                                                                  · exact h070 k h
                                                                                · exact h071 k h
                                                                              · exact h072 k h
                                                                            · exact h073 k h
                                                                          · exact h074 k h
                                                                        · exact h075 k h
                                                                      · exact h076 k h
                                                                    · exact h077 k h
                                                                  · exact h078 k h
                                                                · exact h079 k h
                                                              · exact h080 k h
                                                            · exact h081 k h
                                                          · exact h082 k h
                                                        · exact h083 k h
                                                      · exact h084 k h
                                                    · exact h085 k h
                                                  · exact h086 k h
                                                · exact h087 k h
                                              · exact h088 k h
                                            · exact h089 k h
                                          · exact h090 k h
                                        · exact h091 k h
                                      · exact h092 k h
                                    · exact h093 k h
                                  · exact h094 k h
                                · exact h095 k h
                              · exact h096 k h
                            · exact h097 k h
                          · exact h098 k h
                        · exact h099 k h
                      · exact h100 k h
                    · exact h101 k h
                  · exact h102 k h
                · exact h103 k h
              · exact h104 k h
            · exact h105 k h
          · exact h106 k h
        · exact h107 k h
      · exact h108 k h
    · exact h109 k h
  · exact h110 k h

#print axioms of_batches
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteListAssembly
