/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0853 : Family 10 := level10.get ⟨581,by decide⟩
def sourceMap0853 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0853 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0853_checked : acceptsGraphIso
    (source (graph core0853) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2074.graph sourceMap0853=true := by decide +kernel
theorem fusedMap0853_checked : acceptsGraphIso
    (fused (graph core0853) (root 10) 2 2) DegreeTwoThreeSpectrum5250.graph fusedMap0853=true := by decide +kernel
theorem certified0853 : Certified (graph core0853) (root 10) 2 2 :=
  of_native_maps core0853 DegreeOneMiddleResidualSpectrum2074.graph DegreeTwoThreeSpectrum5250.graph
    sourceMap0853 fusedMap0853 sourceMap0853_checked fusedMap0853_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0853
#print axioms sourceMap0853_checked
#print axioms fusedMap0853_checked
#print axioms certified0853
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
