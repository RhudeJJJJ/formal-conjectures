/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0936 : Family 10 := level10.get ⟨746,by decide⟩
def sourceMap0936 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0936 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0936_checked : acceptsGraphIso
    (source (graph core0936) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2214.graph sourceMap0936=true := by decide +kernel
theorem fusedMap0936_checked : acceptsGraphIso
    (fused (graph core0936) (root 10) 2 2) DegreeTwoThreeSpectrum5508.graph fusedMap0936=true := by decide +kernel
theorem certified0936 : Certified (graph core0936) (root 10) 2 2 :=
  of_native_maps core0936 DegreeOneMiddleResidualSpectrum2214.graph DegreeTwoThreeSpectrum5508.graph
    sourceMap0936 fusedMap0936 sourceMap0936_checked fusedMap0936_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0936
#print axioms sourceMap0936_checked
#print axioms fusedMap0936_checked
#print axioms certified0936
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
