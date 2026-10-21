/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1765 : Family 9 := level9.get ⟨689,by decide⟩
def sourceMap1765 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1765 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1765_checked : acceptsGraphIso
    (source (graph core1765) (root 9) 0 0) SmallGeFourSpectrum198.graph sourceMap1765=true := by decide +kernel
theorem fusedMap1765_checked : acceptsGraphIso
    (fused (graph core1765) (root 9) 0 0) SmallGeFourSpectrum199.graph fusedMap1765=true := by decide +kernel
theorem certified1765 : Certified (graph core1765) (root 9) 0 0 :=
  of_native_maps core1765 SmallGeFourSpectrum198.graph SmallGeFourSpectrum199.graph
    sourceMap1765 fusedMap1765 sourceMap1765_checked fusedMap1765_checked
    DegreeOneSmallComparisons.comparison1765
#print axioms sourceMap1765_checked
#print axioms fusedMap1765_checked
#print axioms certified1765
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
