/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0064 : Family 8 := level8.get ⟨5,by decide⟩
def sourceMap0064 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,3,4,5,6,7,8] (sourceLabel 8 2 2 v)
def fusedMap0064 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0064_checked : acceptsGraphIso
    (source (graph core0064) (root 8) 2 2) DegreeOneMiddleResidualSpectrum247.graph sourceMap0064=true := by decide +kernel
theorem fusedMap0064_checked : acceptsGraphIso
    (fused (graph core0064) (root 8) 2 2) DegreeTwoThreeSpectrum2313.graph fusedMap0064=true := by decide +kernel
theorem certified0064 : Certified (graph core0064) (root 8) 2 2 :=
  of_native_maps core0064 DegreeOneMiddleResidualSpectrum247.graph DegreeTwoThreeSpectrum2313.graph
    sourceMap0064 fusedMap0064 sourceMap0064_checked fusedMap0064_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0064
#print axioms sourceMap0064_checked
#print axioms fusedMap0064_checked
#print axioms certified0064
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
