/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0069 : Family 8 := level8.get ⟨11,by decide⟩
def sourceMap0069 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0069 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0069_checked : acceptsGraphIso
    (source (graph core0069) (root 8) 2 2) DegreeOneMiddleResidualSpectrum204.graph sourceMap0069=true := by decide +kernel
theorem fusedMap0069_checked : acceptsGraphIso
    (fused (graph core0069) (root 8) 2 2) DegreeTwoThreeSpectrum2338.graph fusedMap0069=true := by decide +kernel
theorem certified0069 : Certified (graph core0069) (root 8) 2 2 :=
  of_native_maps core0069 DegreeOneMiddleResidualSpectrum204.graph DegreeTwoThreeSpectrum2338.graph
    sourceMap0069 fusedMap0069 sourceMap0069_checked fusedMap0069_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0069
#print axioms sourceMap0069_checked
#print axioms fusedMap0069_checked
#print axioms certified0069
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
