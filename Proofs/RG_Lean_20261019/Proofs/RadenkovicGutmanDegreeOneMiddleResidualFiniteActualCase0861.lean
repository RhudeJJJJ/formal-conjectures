/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0861 : Family 10 := level10.get ⟨593,by decide⟩
def sourceMap0861 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0861 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0861_checked : acceptsGraphIso
    (source (graph core0861) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2090.graph sourceMap0861=true := by decide +kernel
theorem fusedMap0861_checked : acceptsGraphIso
    (fused (graph core0861) (root 10) 2 2) DegreeTwoThreeSpectrum5267.graph fusedMap0861=true := by decide +kernel
theorem certified0861 : Certified (graph core0861) (root 10) 2 2 :=
  of_native_maps core0861 DegreeOneMiddleResidualSpectrum2090.graph DegreeTwoThreeSpectrum5267.graph
    sourceMap0861 fusedMap0861 sourceMap0861_checked fusedMap0861_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0861
#print axioms sourceMap0861_checked
#print axioms fusedMap0861_checked
#print axioms certified0861
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
