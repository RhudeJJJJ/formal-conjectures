/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0256 : Family 9 := level9.get ⟨75,by decide⟩
def sourceMap0256 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0256 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0256_checked : acceptsGraphIso
    (source (graph core0256) (root 9) 2 2) DegreeOneMiddleResidualSpectrum664.graph sourceMap0256=true := by decide +kernel
theorem fusedMap0256_checked : acceptsGraphIso
    (fused (graph core0256) (root 9) 2 2) DegreeTwoThreeSpectrum4008.graph fusedMap0256=true := by decide +kernel
theorem certified0256 : Certified (graph core0256) (root 9) 2 2 :=
  of_native_maps core0256 DegreeOneMiddleResidualSpectrum664.graph DegreeTwoThreeSpectrum4008.graph
    sourceMap0256 fusedMap0256 sourceMap0256_checked fusedMap0256_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0256
#print axioms sourceMap0256_checked
#print axioms fusedMap0256_checked
#print axioms certified0256
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
