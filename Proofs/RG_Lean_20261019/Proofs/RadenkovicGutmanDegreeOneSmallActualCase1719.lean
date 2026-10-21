/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1719 : Family 9 := level9.get ⟨501,by decide⟩
def sourceMap1719 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,4,5,6,7,8,2,3] (sourceLabel 9 0 0 v)
def fusedMap1719 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1719_checked : acceptsGraphIso
    (source (graph core1719) (root 9) 0 0) SmallGeFourSpectrum141.graph sourceMap1719=true := by decide +kernel
theorem fusedMap1719_checked : acceptsGraphIso
    (fused (graph core1719) (root 9) 0 0) SmallGeFourSpectrum195.graph fusedMap1719=true := by decide +kernel
theorem certified1719 : Certified (graph core1719) (root 9) 0 0 :=
  of_native_maps core1719 SmallGeFourSpectrum141.graph SmallGeFourSpectrum195.graph
    sourceMap1719 fusedMap1719 sourceMap1719_checked fusedMap1719_checked
    DegreeOneSmallComparisons.comparison1719
#print axioms sourceMap1719_checked
#print axioms fusedMap1719_checked
#print axioms certified1719
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
