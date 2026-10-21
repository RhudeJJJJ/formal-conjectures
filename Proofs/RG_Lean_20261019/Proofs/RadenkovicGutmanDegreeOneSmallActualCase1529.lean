/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1529 : Family 9 := level9.get ⟨259,by decide⟩
def sourceMap1529 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1529 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1529_checked : acceptsGraphIso
    (source (graph core1529) (root 9) 0 0) SmallGeFourSpectrum161.graph sourceMap1529=true := by decide +kernel
theorem fusedMap1529_checked : acceptsGraphIso
    (fused (graph core1529) (root 9) 0 0) SmallGeFourSpectrum107.graph fusedMap1529=true := by decide +kernel
theorem certified1529 : Certified (graph core1529) (root 9) 0 0 :=
  of_native_maps core1529 SmallGeFourSpectrum161.graph SmallGeFourSpectrum107.graph
    sourceMap1529 fusedMap1529 sourceMap1529_checked fusedMap1529_checked
    DegreeOneSmallComparisons.comparison1529
#print axioms sourceMap1529_checked
#print axioms fusedMap1529_checked
#print axioms certified1529
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
