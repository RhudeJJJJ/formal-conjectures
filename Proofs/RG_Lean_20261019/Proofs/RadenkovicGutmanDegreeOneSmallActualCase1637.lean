/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1637 : Family 9 := level9.get ⟨378,by decide⟩
def sourceMap1637 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (sourceLabel 9 0 0 v)
def fusedMap1637 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1637_checked : acceptsGraphIso
    (source (graph core1637) (root 9) 0 0) DegreeOneSmallSpectrum713.graph sourceMap1637=true := by decide +kernel
theorem fusedMap1637_checked : acceptsGraphIso
    (fused (graph core1637) (root 9) 0 0) SmallGeFourSpectrum154.graph fusedMap1637=true := by decide +kernel
theorem certified1637 : Certified (graph core1637) (root 9) 0 0 :=
  of_native_maps core1637 DegreeOneSmallSpectrum713.graph SmallGeFourSpectrum154.graph
    sourceMap1637 fusedMap1637 sourceMap1637_checked fusedMap1637_checked
    DegreeOneSmallComparisons.comparison1637
#print axioms sourceMap1637_checked
#print axioms fusedMap1637_checked
#print axioms certified1637
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
