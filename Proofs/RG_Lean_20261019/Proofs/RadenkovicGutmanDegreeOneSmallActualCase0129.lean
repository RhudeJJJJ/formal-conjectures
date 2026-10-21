/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0129 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0129 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,8,5,6,7] (sourceLabel 4 0 2 v)
def fusedMap0129 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap0129_checked : acceptsGraphIso
    (source (graph core0129) (root 4) 0 2) DegreeOneSmallSpectrum060.graph sourceMap0129=true := by decide +kernel
theorem fusedMap0129_checked : acceptsGraphIso
    (fused (graph core0129) (root 4) 0 2) DegreeOneSmallSpectrum035.graph fusedMap0129=true := by decide +kernel
theorem certified0129 : Certified (graph core0129) (root 4) 0 2 :=
  of_native_maps core0129 DegreeOneSmallSpectrum060.graph DegreeOneSmallSpectrum035.graph
    sourceMap0129 fusedMap0129 sourceMap0129_checked fusedMap0129_checked
    DegreeOneSmallComparisons.comparison0129
#print axioms sourceMap0129_checked
#print axioms fusedMap0129_checked
#print axioms certified0129
def sourceMap0129swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 4 2 0 v)
def fusedMap0129swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap0129swap_checked : acceptsGraphIso
    (source (graph core0129) (root 4) 2 0) DegreeOneSmallSpectrum060.graph sourceMap0129swap=true := by decide +kernel
theorem fusedMap0129swap_checked : acceptsGraphIso
    (fused (graph core0129) (root 4) 2 0) DegreeOneSmallSpectrum035.graph fusedMap0129swap=true := by decide +kernel
theorem certified0129swap : Certified (graph core0129) (root 4) 2 0 :=
  of_native_maps core0129 DegreeOneSmallSpectrum060.graph DegreeOneSmallSpectrum035.graph
    sourceMap0129swap fusedMap0129swap sourceMap0129swap_checked fusedMap0129swap_checked
    DegreeOneSmallComparisons.comparison0129
#print axioms sourceMap0129swap_checked
#print axioms fusedMap0129swap_checked
#print axioms certified0129swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
