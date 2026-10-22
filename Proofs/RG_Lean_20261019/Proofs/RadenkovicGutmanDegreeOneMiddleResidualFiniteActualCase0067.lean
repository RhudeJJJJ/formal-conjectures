/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0067 : Family 8 := level8.get ⟨9,by decide⟩
def sourceMap0067 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0067 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0067_checked : acceptsGraphIso
    (source (graph core0067) (root 8) 2 2) DegreeOneMiddleResidualSpectrum197.graph sourceMap0067=true := by decide +kernel
theorem fusedMap0067_checked : acceptsGraphIso
    (fused (graph core0067) (root 8) 2 2) DegreeTwoThreeSpectrum2327.graph fusedMap0067=true := by decide +kernel
theorem certified0067 : Certified (graph core0067) (root 8) 2 2 :=
  of_native_maps core0067 DegreeOneMiddleResidualSpectrum197.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap0067 fusedMap0067 sourceMap0067_checked fusedMap0067_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0067
#print axioms sourceMap0067_checked
#print axioms fusedMap0067_checked
#print axioms certified0067
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
