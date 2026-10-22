/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0026 : Family 7 := level7.get ⟨35,by decide⟩
def sourceMap0026 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0026 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0026_checked : acceptsGraphIso
    (source (graph core0026) (root 7) 2 2) DegreeOneMiddleResidualSpectrum069.graph sourceMap0026=true := by decide +kernel
theorem fusedMap0026_checked : acceptsGraphIso
    (fused (graph core0026) (root 7) 2 2) DegreeTwoThreeSpectrum1781.graph fusedMap0026=true := by decide +kernel
theorem certified0026 : Certified (graph core0026) (root 7) 2 2 :=
  of_native_maps core0026 DegreeOneMiddleResidualSpectrum069.graph DegreeTwoThreeSpectrum1781.graph
    sourceMap0026 fusedMap0026 sourceMap0026_checked fusedMap0026_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0026
#print axioms sourceMap0026_checked
#print axioms fusedMap0026_checked
#print axioms certified0026
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
