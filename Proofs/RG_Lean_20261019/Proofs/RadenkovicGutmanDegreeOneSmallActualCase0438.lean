/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0438 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0438 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (sourceLabel 6 0 0 v)
def fusedMap0438 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0438_checked : acceptsGraphIso
    (source (graph core0438) (root 6) 0 0) SmallGeFourSpectrum009.graph sourceMap0438=true := by decide +kernel
theorem fusedMap0438_checked : acceptsGraphIso
    (fused (graph core0438) (root 6) 0 0) SmallGeFourSpectrum010.graph fusedMap0438=true := by decide +kernel
theorem certified0438 : Certified (graph core0438) (root 6) 0 0 :=
  of_native_maps core0438 SmallGeFourSpectrum009.graph SmallGeFourSpectrum010.graph
    sourceMap0438 fusedMap0438 sourceMap0438_checked fusedMap0438_checked
    DegreeOneSmallComparisons.comparison0438
#print axioms sourceMap0438_checked
#print axioms fusedMap0438_checked
#print axioms certified0438
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
