/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0063 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap0063 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0063 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0063_checked : acceptsGraphIso
    (source (graph core0063) (root 7) 0 0) DegreeOneSmallSpectrum157.graph sourceMap0063=true := by decide +kernel
theorem fusedMap0063_checked : acceptsGraphIso
    (fused (graph core0063) (root 7) 0 0) DegreeOneSmallSpectrum156.graph fusedMap0063=true := by decide +kernel
theorem certified0063 : Certified (graph core0063) (root 7) 0 0 :=
  of_native_maps core0063 DegreeOneSmallSpectrum157.graph DegreeOneSmallSpectrum156.graph
    sourceMap0063 fusedMap0063 sourceMap0063_checked fusedMap0063_checked
    DegreeTwoThreeFiniteComparisons.comparison0063
#print axioms sourceMap0063_checked
#print axioms fusedMap0063_checked
#print axioms certified0063
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
