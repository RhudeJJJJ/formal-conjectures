/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0799 : Family 8 := level8.get ⟨18,by decide⟩
def sourceMap0799 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0799 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0799_checked : acceptsGraphIso
    (source (graph core0799) (root 8) 0 0) DegreeOneSmallSpectrum180.graph sourceMap0799=true := by decide +kernel
theorem fusedMap0799_checked : acceptsGraphIso
    (fused (graph core0799) (root 8) 0 0) DegreeOneSmallSpectrum216.graph fusedMap0799=true := by decide +kernel
theorem certified0799 : Certified (graph core0799) (root 8) 0 0 :=
  of_native_maps core0799 DegreeOneSmallSpectrum180.graph DegreeOneSmallSpectrum216.graph
    sourceMap0799 fusedMap0799 sourceMap0799_checked fusedMap0799_checked
    DegreeOneSmallComparisons.comparison0799
#print axioms sourceMap0799_checked
#print axioms fusedMap0799_checked
#print axioms certified0799
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
