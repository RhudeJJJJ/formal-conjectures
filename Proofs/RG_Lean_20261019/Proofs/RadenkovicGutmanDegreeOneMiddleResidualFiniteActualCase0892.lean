/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0892 : Family 10 := level10.get ⟨655,by decide⟩
def sourceMap0892 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0892 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0892_checked : acceptsGraphIso
    (source (graph core0892) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2135.graph sourceMap0892=true := by decide +kernel
theorem fusedMap0892_checked : acceptsGraphIso
    (fused (graph core0892) (root 10) 2 2) DegreeTwoThreeSpectrum5364.graph fusedMap0892=true := by decide +kernel
theorem certified0892 : Certified (graph core0892) (root 10) 2 2 :=
  of_native_maps core0892 DegreeOneMiddleResidualSpectrum2135.graph DegreeTwoThreeSpectrum5364.graph
    sourceMap0892 fusedMap0892 sourceMap0892_checked fusedMap0892_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0892
#print axioms sourceMap0892_checked
#print axioms fusedMap0892_checked
#print axioms certified0892
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
