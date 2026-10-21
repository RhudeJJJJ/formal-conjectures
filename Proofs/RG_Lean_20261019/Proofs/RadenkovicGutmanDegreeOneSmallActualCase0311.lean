/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0311 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0311 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 6 2 2 v)
def fusedMap0311 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0311_checked : acceptsGraphIso
    (source (graph core0311) (root 6) 2 2) DegreeOneSmallSpectrum1463.graph sourceMap0311=true := by decide +kernel
theorem fusedMap0311_checked : acceptsGraphIso
    (fused (graph core0311) (root 6) 2 2) DegreeOneSmallSpectrum859.graph fusedMap0311=true := by decide +kernel
theorem certified0311 : Certified (graph core0311) (root 6) 2 2 :=
  of_native_maps core0311 DegreeOneSmallSpectrum1463.graph DegreeOneSmallSpectrum859.graph
    sourceMap0311 fusedMap0311 sourceMap0311_checked fusedMap0311_checked
    DegreeOneSmallComparisons.comparison0311
#print axioms sourceMap0311_checked
#print axioms fusedMap0311_checked
#print axioms certified0311
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
