/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0181 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0181 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11] (sourceLabel 5 2 2 v)
def fusedMap0181 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0181_checked : acceptsGraphIso
    (source (graph core0181) (root 5) 2 2) DegreeOneSmallSpectrum491.graph sourceMap0181=true := by decide +kernel
theorem fusedMap0181_checked : acceptsGraphIso
    (fused (graph core0181) (root 5) 2 2) DegreeOneSmallSpectrum378.graph fusedMap0181=true := by decide +kernel
theorem certified0181 : Certified (graph core0181) (root 5) 2 2 :=
  of_native_maps core0181 DegreeOneSmallSpectrum491.graph DegreeOneSmallSpectrum378.graph
    sourceMap0181 fusedMap0181 sourceMap0181_checked fusedMap0181_checked
    DegreeOneSmallComparisons.comparison0181
#print axioms sourceMap0181_checked
#print axioms fusedMap0181_checked
#print axioms certified0181
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
