/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1571 : Family 9 := level9.get ⟨317,by decide⟩
def sourceMap1571 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1571 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1571_checked : acceptsGraphIso
    (source (graph core1571) (root 9) 0 0) SmallGeFourSpectrum114.graph sourceMap1571=true := by decide +kernel
theorem fusedMap1571_checked : acceptsGraphIso
    (fused (graph core1571) (root 9) 0 0) SmallGeFourSpectrum116.graph fusedMap1571=true := by decide +kernel
theorem certified1571 : Certified (graph core1571) (root 9) 0 0 :=
  of_native_maps core1571 SmallGeFourSpectrum114.graph SmallGeFourSpectrum116.graph
    sourceMap1571 fusedMap1571 sourceMap1571_checked fusedMap1571_checked
    DegreeOneSmallComparisons.comparison1571
#print axioms sourceMap1571_checked
#print axioms fusedMap1571_checked
#print axioms certified1571
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
