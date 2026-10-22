/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0485 : Family 10 := level10.get ⟨1,by decide⟩
def sourceMap0485 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0485 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0485_checked : acceptsGraphIso
    (source (graph core0485) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1231.graph sourceMap0485=true := by decide +kernel
theorem fusedMap0485_checked : acceptsGraphIso
    (fused (graph core0485) (root 10) 2 2) DegreeTwoThreeSpectrum4959.graph fusedMap0485=true := by decide +kernel
theorem certified0485 : Certified (graph core0485) (root 10) 2 2 :=
  of_native_maps core0485 DegreeOneMiddleResidualSpectrum1231.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap0485 fusedMap0485 sourceMap0485_checked fusedMap0485_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0485
#print axioms sourceMap0485_checked
#print axioms fusedMap0485_checked
#print axioms certified0485
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
