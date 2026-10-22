/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0363 : Family 9 := level9.get ⟨256,by decide⟩
def sourceMap0363 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0363 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0363_checked : acceptsGraphIso
    (source (graph core0363) (root 9) 2 2) DegreeOneMiddleResidualSpectrum880.graph sourceMap0363=true := by decide +kernel
theorem fusedMap0363_checked : acceptsGraphIso
    (fused (graph core0363) (root 9) 2 2) DegreeTwoThreeSpectrum4065.graph fusedMap0363=true := by decide +kernel
theorem certified0363 : Certified (graph core0363) (root 9) 2 2 :=
  of_native_maps core0363 DegreeOneMiddleResidualSpectrum880.graph DegreeTwoThreeSpectrum4065.graph
    sourceMap0363 fusedMap0363 sourceMap0363_checked fusedMap0363_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0363
#print axioms sourceMap0363_checked
#print axioms fusedMap0363_checked
#print axioms certified0363
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
