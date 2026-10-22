/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0955 : Family 10 := level10.get ⟨783,by decide⟩
def sourceMap0955 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0955 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0955_checked : acceptsGraphIso
    (source (graph core0955) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2243.graph sourceMap0955=true := by decide +kernel
theorem fusedMap0955_checked : acceptsGraphIso
    (fused (graph core0955) (root 10) 2 2) DegreeTwoThreeSpectrum5564.graph fusedMap0955=true := by decide +kernel
theorem certified0955 : Certified (graph core0955) (root 10) 2 2 :=
  of_native_maps core0955 DegreeOneMiddleResidualSpectrum2243.graph DegreeTwoThreeSpectrum5564.graph
    sourceMap0955 fusedMap0955 sourceMap0955_checked fusedMap0955_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0955
#print axioms sourceMap0955_checked
#print axioms fusedMap0955_checked
#print axioms certified0955
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
