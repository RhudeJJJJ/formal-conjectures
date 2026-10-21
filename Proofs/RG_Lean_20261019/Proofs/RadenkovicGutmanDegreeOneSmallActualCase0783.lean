/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0783 : Family 8 := level8.get ⟨14,by decide⟩
def sourceMap0783 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0783 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0783_checked : acceptsGraphIso
    (source (graph core0783) (root 8) 0 0) DegreeOneSmallSpectrum190.graph sourceMap0783=true := by decide +kernel
theorem fusedMap0783_checked : acceptsGraphIso
    (fused (graph core0783) (root 8) 0 0) DegreeOneSmallSpectrum202.graph fusedMap0783=true := by decide +kernel
theorem certified0783 : Certified (graph core0783) (root 8) 0 0 :=
  of_native_maps core0783 DegreeOneSmallSpectrum190.graph DegreeOneSmallSpectrum202.graph
    sourceMap0783 fusedMap0783 sourceMap0783_checked fusedMap0783_checked
    DegreeOneSmallComparisons.comparison0783
#print axioms sourceMap0783_checked
#print axioms fusedMap0783_checked
#print axioms certified0783
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
