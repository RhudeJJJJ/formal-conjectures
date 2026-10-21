/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0787 : Family 8 := level8.get ⟨15,by decide⟩
def sourceMap0787 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0787 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0787_checked : acceptsGraphIso
    (source (graph core0787) (root 8) 0 0) DegreeOneSmallSpectrum191.graph sourceMap0787=true := by decide +kernel
theorem fusedMap0787_checked : acceptsGraphIso
    (fused (graph core0787) (root 8) 0 0) DegreeOneSmallSpectrum207.graph fusedMap0787=true := by decide +kernel
theorem certified0787 : Certified (graph core0787) (root 8) 0 0 :=
  of_native_maps core0787 DegreeOneSmallSpectrum191.graph DegreeOneSmallSpectrum207.graph
    sourceMap0787 fusedMap0787 sourceMap0787_checked fusedMap0787_checked
    DegreeOneSmallComparisons.comparison0787
#print axioms sourceMap0787_checked
#print axioms fusedMap0787_checked
#print axioms certified0787
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
