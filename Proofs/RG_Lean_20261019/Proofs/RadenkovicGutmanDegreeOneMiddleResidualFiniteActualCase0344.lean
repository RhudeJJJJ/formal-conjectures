/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0344 : Family 9 := level9.get ⟨219,by decide⟩
def sourceMap0344 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0344 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0344_checked : acceptsGraphIso
    (source (graph core0344) (root 9) 2 2) DegreeOneMiddleResidualSpectrum848.graph sourceMap0344=true := by decide +kernel
theorem fusedMap0344_checked : acceptsGraphIso
    (fused (graph core0344) (root 9) 2 2) DegreeTwoThreeSpectrum4006.graph fusedMap0344=true := by decide +kernel
theorem certified0344 : Certified (graph core0344) (root 9) 2 2 :=
  of_native_maps core0344 DegreeOneMiddleResidualSpectrum848.graph DegreeTwoThreeSpectrum4006.graph
    sourceMap0344 fusedMap0344 sourceMap0344_checked fusedMap0344_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0344
#print axioms sourceMap0344_checked
#print axioms fusedMap0344_checked
#print axioms certified0344
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
