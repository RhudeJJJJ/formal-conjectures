/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0386 : Family 9 := level9.get ⟨317,by decide⟩
def sourceMap0386 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0386 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0386_checked : acceptsGraphIso
    (source (graph core0386) (root 9) 2 2) DegreeOneMiddleResidualSpectrum737.graph sourceMap0386=true := by decide +kernel
theorem fusedMap0386_checked : acceptsGraphIso
    (fused (graph core0386) (root 9) 2 2) DegreeOneMiddleResidualSpectrum554.graph fusedMap0386=true := by decide +kernel
theorem certified0386 : Certified (graph core0386) (root 9) 2 2 :=
  of_native_maps core0386 DegreeOneMiddleResidualSpectrum737.graph DegreeOneMiddleResidualSpectrum554.graph
    sourceMap0386 fusedMap0386 sourceMap0386_checked fusedMap0386_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0386
#print axioms sourceMap0386_checked
#print axioms fusedMap0386_checked
#print axioms certified0386
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
