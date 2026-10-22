/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0700 : Family 10 := level10.get ⟨307,by decide⟩
def sourceMap0700 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0700 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0700_checked : acceptsGraphIso
    (source (graph core0700) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1761.graph sourceMap0700=true := by decide +kernel
theorem fusedMap0700_checked : acceptsGraphIso
    (fused (graph core0700) (root 10) 2 2) DegreeTwoThreeSpectrum5496.graph fusedMap0700=true := by decide +kernel
theorem certified0700 : Certified (graph core0700) (root 10) 2 2 :=
  of_native_maps core0700 DegreeOneMiddleResidualSpectrum1761.graph DegreeTwoThreeSpectrum5496.graph
    sourceMap0700 fusedMap0700 sourceMap0700_checked fusedMap0700_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0700
#print axioms sourceMap0700_checked
#print axioms fusedMap0700_checked
#print axioms certified0700
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
