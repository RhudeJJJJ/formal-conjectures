/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1029 : Family 8 := level8.get ⟨112,by decide⟩
def sourceMap1029 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1029 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1029_checked : acceptsGraphIso
    (source (graph core1029) (root 8) 0 2) DegreeOneSmallSpectrum1117.graph sourceMap1029=true := by decide +kernel
theorem fusedMap1029_checked : acceptsGraphIso
    (fused (graph core1029) (root 8) 0 2) DegreeOneSmallSpectrum1118.graph fusedMap1029=true := by decide +kernel
theorem certified1029 : Certified (graph core1029) (root 8) 0 2 :=
  of_native_maps core1029 DegreeOneSmallSpectrum1117.graph DegreeOneSmallSpectrum1118.graph
    sourceMap1029 fusedMap1029 sourceMap1029_checked fusedMap1029_checked
    DegreeOneSmallComparisons.comparison1029
#print axioms sourceMap1029_checked
#print axioms fusedMap1029_checked
#print axioms certified1029
def sourceMap1029swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1029swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1029swap_checked : acceptsGraphIso
    (source (graph core1029) (root 8) 2 0) DegreeOneSmallSpectrum1117.graph sourceMap1029swap=true := by decide +kernel
theorem fusedMap1029swap_checked : acceptsGraphIso
    (fused (graph core1029) (root 8) 2 0) DegreeOneSmallSpectrum1118.graph fusedMap1029swap=true := by decide +kernel
theorem certified1029swap : Certified (graph core1029) (root 8) 2 0 :=
  of_native_maps core1029 DegreeOneSmallSpectrum1117.graph DegreeOneSmallSpectrum1118.graph
    sourceMap1029swap fusedMap1029swap sourceMap1029swap_checked fusedMap1029swap_checked
    DegreeOneSmallComparisons.comparison1029
#print axioms sourceMap1029swap_checked
#print axioms fusedMap1029swap_checked
#print axioms certified1029swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
