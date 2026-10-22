/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0636 : Family 10 := level10.get ⟨207,by decide⟩
def sourceMap0636 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0636 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0636_checked : acceptsGraphIso
    (source (graph core0636) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1586.graph sourceMap0636=true := by decide +kernel
theorem fusedMap0636_checked : acceptsGraphIso
    (fused (graph core0636) (root 10) 2 2) DegreeTwoThreeSpectrum5207.graph fusedMap0636=true := by decide +kernel
theorem certified0636 : Certified (graph core0636) (root 10) 2 2 :=
  of_native_maps core0636 DegreeOneMiddleResidualSpectrum1586.graph DegreeTwoThreeSpectrum5207.graph
    sourceMap0636 fusedMap0636 sourceMap0636_checked fusedMap0636_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0636
#print axioms sourceMap0636_checked
#print axioms fusedMap0636_checked
#print axioms certified0636
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
