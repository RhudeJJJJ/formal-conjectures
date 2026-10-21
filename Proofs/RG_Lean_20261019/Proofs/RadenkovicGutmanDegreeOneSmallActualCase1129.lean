/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1129 : Family 8 := level8.get ⟨167,by decide⟩
def sourceMap1129 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1129 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1129_checked : acceptsGraphIso
    (source (graph core1129) (root 8) 0 2) DegreeOneSmallSpectrum1480.graph sourceMap1129=true := by decide +kernel
theorem fusedMap1129_checked : acceptsGraphIso
    (fused (graph core1129) (root 8) 0 2) DegreeOneSmallSpectrum1481.graph fusedMap1129=true := by decide +kernel
theorem certified1129 : Certified (graph core1129) (root 8) 0 2 :=
  of_native_maps core1129 DegreeOneSmallSpectrum1480.graph DegreeOneSmallSpectrum1481.graph
    sourceMap1129 fusedMap1129 sourceMap1129_checked fusedMap1129_checked
    DegreeOneSmallComparisons.comparison1129
#print axioms sourceMap1129_checked
#print axioms fusedMap1129_checked
#print axioms certified1129
def sourceMap1129swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1129swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1129swap_checked : acceptsGraphIso
    (source (graph core1129) (root 8) 2 0) DegreeOneSmallSpectrum1480.graph sourceMap1129swap=true := by decide +kernel
theorem fusedMap1129swap_checked : acceptsGraphIso
    (fused (graph core1129) (root 8) 2 0) DegreeOneSmallSpectrum1481.graph fusedMap1129swap=true := by decide +kernel
theorem certified1129swap : Certified (graph core1129) (root 8) 2 0 :=
  of_native_maps core1129 DegreeOneSmallSpectrum1480.graph DegreeOneSmallSpectrum1481.graph
    sourceMap1129swap fusedMap1129swap sourceMap1129swap_checked fusedMap1129swap_checked
    DegreeOneSmallComparisons.comparison1129
#print axioms sourceMap1129swap_checked
#print axioms fusedMap1129swap_checked
#print axioms certified1129swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
