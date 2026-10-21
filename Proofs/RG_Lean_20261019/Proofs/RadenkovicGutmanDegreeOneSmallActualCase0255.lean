/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0255 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0255 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![5,0,1,2,3,4,6,7] (sourceLabel 5 0 0 v)
def fusedMap0255 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 5 0 0 v)
theorem sourceMap0255_checked : acceptsGraphIso
    (source (graph core0255) (root 5) 0 0) DegreeOneSmallSpectrum027.graph sourceMap0255=true := by decide +kernel
theorem fusedMap0255_checked : acceptsGraphIso
    (fused (graph core0255) (root 5) 0 0) SmallGeFourSpectrum003.graph fusedMap0255=true := by decide +kernel
theorem certified0255 : Certified (graph core0255) (root 5) 0 0 :=
  of_native_maps core0255 DegreeOneSmallSpectrum027.graph SmallGeFourSpectrum003.graph
    sourceMap0255 fusedMap0255 sourceMap0255_checked fusedMap0255_checked
    DegreeOneSmallComparisons.comparison0255
#print axioms sourceMap0255_checked
#print axioms fusedMap0255_checked
#print axioms certified0255
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
