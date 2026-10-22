/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0266 : Family 9 := level9.get ⟨88,by decide⟩
def sourceMap0266 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0266 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0266_checked : acceptsGraphIso
    (source (graph core0266) (root 9) 2 2) DegreeOneMiddleResidualSpectrum684.graph sourceMap0266=true := by decide +kernel
theorem fusedMap0266_checked : acceptsGraphIso
    (fused (graph core0266) (root 9) 2 2) DegreeTwoThreeSpectrum4051.graph fusedMap0266=true := by decide +kernel
theorem certified0266 : Certified (graph core0266) (root 9) 2 2 :=
  of_native_maps core0266 DegreeOneMiddleResidualSpectrum684.graph DegreeTwoThreeSpectrum4051.graph
    sourceMap0266 fusedMap0266 sourceMap0266_checked fusedMap0266_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0266
#print axioms sourceMap0266_checked
#print axioms fusedMap0266_checked
#print axioms certified0266
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
