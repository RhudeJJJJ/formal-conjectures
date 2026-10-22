/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0984 : Family 10 := level10.get ⟨1657,by decide⟩
def sourceMap0984 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0984 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0984_checked : acceptsGraphIso
    (source (graph core0984) (root 10) 0 0) DegreeOneSmallSpectrum1648.graph sourceMap0984=true := by decide +kernel
theorem fusedMap0984_checked : acceptsGraphIso
    (fused (graph core0984) (root 10) 0 0) DegreeOneSmallSpectrum1631.graph fusedMap0984=true := by decide +kernel
theorem certified0984 : Certified (graph core0984) (root 10) 0 0 :=
  of_native_maps core0984 DegreeOneSmallSpectrum1648.graph DegreeOneSmallSpectrum1631.graph
    sourceMap0984 fusedMap0984 sourceMap0984_checked fusedMap0984_checked
    DegreeTwoThreeFiniteComparisons.comparison0984
#print axioms sourceMap0984_checked
#print axioms fusedMap0984_checked
#print axioms certified0984
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
