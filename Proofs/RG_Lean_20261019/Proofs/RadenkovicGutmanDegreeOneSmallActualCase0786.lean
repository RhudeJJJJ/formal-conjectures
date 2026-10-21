/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0786 : Family 8 := level8.get ⟨14,by decide⟩
def sourceMap0786 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0786 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0786_checked : acceptsGraphIso
    (source (graph core0786) (root 8) 1 1) DegreeOneSmallSpectrum1332.graph sourceMap0786=true := by decide +kernel
theorem fusedMap0786_checked : acceptsGraphIso
    (fused (graph core0786) (root 8) 1 1) DegreeOneSmallSpectrum915.graph fusedMap0786=true := by decide +kernel
theorem certified0786 : Certified (graph core0786) (root 8) 1 1 :=
  of_native_maps core0786 DegreeOneSmallSpectrum1332.graph DegreeOneSmallSpectrum915.graph
    sourceMap0786 fusedMap0786 sourceMap0786_checked fusedMap0786_checked
    DegreeOneSmallComparisons.comparison0786
#print axioms sourceMap0786_checked
#print axioms fusedMap0786_checked
#print axioms certified0786
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
