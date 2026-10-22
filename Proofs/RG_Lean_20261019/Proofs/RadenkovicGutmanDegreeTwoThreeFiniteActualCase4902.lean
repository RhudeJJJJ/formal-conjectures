/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4902 : Family 10 := level10.get ⟨1374,by decide⟩
def sourceMap4902 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4902 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4902_checked : acceptsGraphIso
    (source (graph core4902) (root 10) 2 2) DegreeTwoThreeSpectrum7452.graph sourceMap4902=true := by decide +kernel
theorem fusedMap4902_checked : acceptsGraphIso
    (fused (graph core4902) (root 10) 2 2) DegreeTwoThreeSpectrum6720.graph fusedMap4902=true := by decide +kernel
theorem certified4902 : Certified (graph core4902) (root 10) 2 2 :=
  of_native_maps core4902 DegreeTwoThreeSpectrum7452.graph DegreeTwoThreeSpectrum6720.graph
    sourceMap4902 fusedMap4902 sourceMap4902_checked fusedMap4902_checked
    DegreeTwoThreeFiniteComparisons.comparison4902
#print axioms sourceMap4902_checked
#print axioms fusedMap4902_checked
#print axioms certified4902
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
