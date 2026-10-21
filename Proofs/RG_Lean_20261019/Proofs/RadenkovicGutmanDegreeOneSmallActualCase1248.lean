/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1248 : Family 9 := level9.get ⟨30,by decide⟩
def sourceMap1248 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1248 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1248_checked : acceptsGraphIso
    (source (graph core1248) (root 9) 0 1) DegreeOneSmallSpectrum942.graph sourceMap1248=true := by decide +kernel
theorem fusedMap1248_checked : acceptsGraphIso
    (fused (graph core1248) (root 9) 0 1) DegreeOneSmallSpectrum974.graph fusedMap1248=true := by decide +kernel
theorem certified1248 : Certified (graph core1248) (root 9) 0 1 :=
  of_native_maps core1248 DegreeOneSmallSpectrum942.graph DegreeOneSmallSpectrum974.graph
    sourceMap1248 fusedMap1248 sourceMap1248_checked fusedMap1248_checked
    DegreeOneSmallComparisons.comparison1248
#print axioms sourceMap1248_checked
#print axioms fusedMap1248_checked
#print axioms certified1248
def sourceMap1248swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1248swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1248swap_checked : acceptsGraphIso
    (source (graph core1248) (root 9) 1 0) DegreeOneSmallSpectrum942.graph sourceMap1248swap=true := by decide +kernel
theorem fusedMap1248swap_checked : acceptsGraphIso
    (fused (graph core1248) (root 9) 1 0) DegreeOneSmallSpectrum974.graph fusedMap1248swap=true := by decide +kernel
theorem certified1248swap : Certified (graph core1248) (root 9) 1 0 :=
  of_native_maps core1248 DegreeOneSmallSpectrum942.graph DegreeOneSmallSpectrum974.graph
    sourceMap1248swap fusedMap1248swap sourceMap1248swap_checked fusedMap1248swap_checked
    DegreeOneSmallComparisons.comparison1248
#print axioms sourceMap1248swap_checked
#print axioms fusedMap1248swap_checked
#print axioms certified1248swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
