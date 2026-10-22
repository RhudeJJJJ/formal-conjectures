/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0553 : Family 10 := level10.get ⟨87,by decide⟩
def sourceMap0553 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0553 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0553_checked : acceptsGraphIso
    (source (graph core0553) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1728.graph sourceMap0553=true := by decide +kernel
theorem fusedMap0553_checked : acceptsGraphIso
    (fused (graph core0553) (root 10) 2 2) DegreeTwoThreeSpectrum5008.graph fusedMap0553=true := by decide +kernel
theorem certified0553 : Certified (graph core0553) (root 10) 2 2 :=
  of_native_maps core0553 DegreeOneMiddleResidualSpectrum1728.graph DegreeTwoThreeSpectrum5008.graph
    sourceMap0553 fusedMap0553 sourceMap0553_checked fusedMap0553_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0553
#print axioms sourceMap0553_checked
#print axioms fusedMap0553_checked
#print axioms certified0553
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
