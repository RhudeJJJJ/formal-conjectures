/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0776 : Family 10 := level10.get ⟨1156,by decide⟩
def sourceMap0776 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0776 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0776_checked : acceptsGraphIso
    (source (graph core0776) (root 10) 0 0) DegreeOneSmallSpectrum1827.graph sourceMap0776=true := by decide +kernel
theorem fusedMap0776_checked : acceptsGraphIso
    (fused (graph core0776) (root 10) 0 0) DegreeOneSmallSpectrum1822.graph fusedMap0776=true := by decide +kernel
theorem certified0776 : Certified (graph core0776) (root 10) 0 0 :=
  of_native_maps core0776 DegreeOneSmallSpectrum1827.graph DegreeOneSmallSpectrum1822.graph
    sourceMap0776 fusedMap0776 sourceMap0776_checked fusedMap0776_checked
    DegreeTwoThreeFiniteComparisons.comparison0776
#print axioms sourceMap0776_checked
#print axioms fusedMap0776_checked
#print axioms certified0776
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
