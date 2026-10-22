/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0966 : Family 10 := level10.get ⟨806,by decide⟩
def sourceMap0966 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0966 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0966_checked : acceptsGraphIso
    (source (graph core0966) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2254.graph sourceMap0966=true := by decide +kernel
theorem fusedMap0966_checked : acceptsGraphIso
    (fused (graph core0966) (root 10) 2 2) DegreeTwoThreeSpectrum5603.graph fusedMap0966=true := by decide +kernel
theorem certified0966 : Certified (graph core0966) (root 10) 2 2 :=
  of_native_maps core0966 DegreeOneMiddleResidualSpectrum2254.graph DegreeTwoThreeSpectrum5603.graph
    sourceMap0966 fusedMap0966 sourceMap0966_checked fusedMap0966_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0966
#print axioms sourceMap0966_checked
#print axioms fusedMap0966_checked
#print axioms certified0966
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
