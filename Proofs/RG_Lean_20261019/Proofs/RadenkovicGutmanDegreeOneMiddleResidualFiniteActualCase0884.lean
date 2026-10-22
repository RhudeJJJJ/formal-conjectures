/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0884 : Family 10 := level10.get ⟨636,by decide⟩
def sourceMap0884 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0884 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0884_checked : acceptsGraphIso
    (source (graph core0884) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2127.graph sourceMap0884=true := by decide +kernel
theorem fusedMap0884_checked : acceptsGraphIso
    (fused (graph core0884) (root 10) 2 2) DegreeTwoThreeSpectrum5330.graph fusedMap0884=true := by decide +kernel
theorem certified0884 : Certified (graph core0884) (root 10) 2 2 :=
  of_native_maps core0884 DegreeOneMiddleResidualSpectrum2127.graph DegreeTwoThreeSpectrum5330.graph
    sourceMap0884 fusedMap0884 sourceMap0884_checked fusedMap0884_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0884
#print axioms sourceMap0884_checked
#print axioms fusedMap0884_checked
#print axioms certified0884
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
