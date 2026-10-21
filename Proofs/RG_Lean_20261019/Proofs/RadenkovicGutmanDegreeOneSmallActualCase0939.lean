/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0939 : Family 8 := level8.get ⟨71,by decide⟩
def sourceMap0939 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0939 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0939_checked : acceptsGraphIso
    (source (graph core0939) (root 8) 0 0) DegreeOneSmallSpectrum313.graph sourceMap0939=true := by decide +kernel
theorem fusedMap0939_checked : acceptsGraphIso
    (fused (graph core0939) (root 8) 0 0) DegreeOneSmallSpectrum219.graph fusedMap0939=true := by decide +kernel
theorem certified0939 : Certified (graph core0939) (root 8) 0 0 :=
  of_native_maps core0939 DegreeOneSmallSpectrum313.graph DegreeOneSmallSpectrum219.graph
    sourceMap0939 fusedMap0939 sourceMap0939_checked fusedMap0939_checked
    DegreeOneSmallComparisons.comparison0939
#print axioms sourceMap0939_checked
#print axioms fusedMap0939_checked
#print axioms certified0939
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
