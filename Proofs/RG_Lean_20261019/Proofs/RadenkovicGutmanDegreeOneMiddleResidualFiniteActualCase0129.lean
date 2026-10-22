/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0129 : Family 8 := level8.get ⟨108,by decide⟩
def sourceMap0129 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0129 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0129_checked : acceptsGraphIso
    (source (graph core0129) (root 8) 2 2) DegreeOneMiddleResidualSpectrum276.graph sourceMap0129=true := by decide +kernel
theorem fusedMap0129_checked : acceptsGraphIso
    (fused (graph core0129) (root 8) 2 2) DegreeTwoThreeSpectrum2505.graph fusedMap0129=true := by decide +kernel
theorem certified0129 : Certified (graph core0129) (root 8) 2 2 :=
  of_native_maps core0129 DegreeOneMiddleResidualSpectrum276.graph DegreeTwoThreeSpectrum2505.graph
    sourceMap0129 fusedMap0129 sourceMap0129_checked fusedMap0129_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0129
#print axioms sourceMap0129_checked
#print axioms fusedMap0129_checked
#print axioms certified0129
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
