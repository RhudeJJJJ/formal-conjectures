/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0665 : Family 10 := level10.get ⟨248,by decide⟩
def sourceMap0665 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0665 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0665_checked : acceptsGraphIso
    (source (graph core0665) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1676.graph sourceMap0665=true := by decide +kernel
theorem fusedMap0665_checked : acceptsGraphIso
    (fused (graph core0665) (root 10) 2 2) DegreeTwoThreeSpectrum5336.graph fusedMap0665=true := by decide +kernel
theorem certified0665 : Certified (graph core0665) (root 10) 2 2 :=
  of_native_maps core0665 DegreeOneMiddleResidualSpectrum1676.graph DegreeTwoThreeSpectrum5336.graph
    sourceMap0665 fusedMap0665 sourceMap0665_checked fusedMap0665_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0665
#print axioms sourceMap0665_checked
#print axioms fusedMap0665_checked
#print axioms certified0665
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
