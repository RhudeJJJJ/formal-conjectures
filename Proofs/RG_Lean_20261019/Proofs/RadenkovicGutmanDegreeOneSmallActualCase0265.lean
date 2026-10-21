/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0265 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0265 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap0265 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0265_checked : acceptsGraphIso
    (source (graph core0265) (root 5) 2 2) DegreeOneSmallSpectrum824.graph sourceMap0265=true := by decide +kernel
theorem fusedMap0265_checked : acceptsGraphIso
    (fused (graph core0265) (root 5) 2 2) SmallGeFourSpectrum094.graph fusedMap0265=true := by decide +kernel
theorem certified0265 : Certified (graph core0265) (root 5) 2 2 :=
  of_native_maps core0265 DegreeOneSmallSpectrum824.graph SmallGeFourSpectrum094.graph
    sourceMap0265 fusedMap0265 sourceMap0265_checked fusedMap0265_checked
    DegreeOneSmallComparisons.comparison0265
#print axioms sourceMap0265_checked
#print axioms fusedMap0265_checked
#print axioms certified0265
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
