/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0857 : Family 10 := level10.get ⟨586,by decide⟩
def sourceMap0857 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0857 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0857_checked : acceptsGraphIso
    (source (graph core0857) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2079.graph sourceMap0857=true := by decide +kernel
theorem fusedMap0857_checked : acceptsGraphIso
    (fused (graph core0857) (root 10) 2 2) DegreeTwoThreeSpectrum5256.graph fusedMap0857=true := by decide +kernel
theorem certified0857 : Certified (graph core0857) (root 10) 2 2 :=
  of_native_maps core0857 DegreeOneMiddleResidualSpectrum2079.graph DegreeTwoThreeSpectrum5256.graph
    sourceMap0857 fusedMap0857 sourceMap0857_checked fusedMap0857_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0857
#print axioms sourceMap0857_checked
#print axioms fusedMap0857_checked
#print axioms certified0857
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
