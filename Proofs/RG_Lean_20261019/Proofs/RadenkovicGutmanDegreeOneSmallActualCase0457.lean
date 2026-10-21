/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0457 : Family 7 := level7.get ⟨1,by decide⟩
def sourceMap0457 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0457 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0457_checked : acceptsGraphIso
    (source (graph core0457) (root 7) 1 1) DegreeOneSmallSpectrum483.graph sourceMap0457=true := by decide +kernel
theorem fusedMap0457_checked : acceptsGraphIso
    (fused (graph core0457) (root 7) 1 1) DegreeOneSmallSpectrum378.graph fusedMap0457=true := by decide +kernel
theorem certified0457 : Certified (graph core0457) (root 7) 1 1 :=
  of_native_maps core0457 DegreeOneSmallSpectrum483.graph DegreeOneSmallSpectrum378.graph
    sourceMap0457 fusedMap0457 sourceMap0457_checked fusedMap0457_checked
    DegreeOneSmallComparisons.comparison0457
#print axioms sourceMap0457_checked
#print axioms fusedMap0457_checked
#print axioms certified0457
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
