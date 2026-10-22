/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4914 : Family 10 := level10.get ⟨1398,by decide⟩
def sourceMap4914 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![5,0,1,2,3,4,12,13,14,15,16,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4914 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4914_checked : acceptsGraphIso
    (source (graph core4914) (root 10) 2 2) DegreeTwoThreeSpectrum7465.graph sourceMap4914=true := by decide +kernel
theorem fusedMap4914_checked : acceptsGraphIso
    (fused (graph core4914) (root 10) 2 2) DegreeTwoThreeSpectrum6767.graph fusedMap4914=true := by decide +kernel
theorem certified4914 : Certified (graph core4914) (root 10) 2 2 :=
  of_native_maps core4914 DegreeTwoThreeSpectrum7465.graph DegreeTwoThreeSpectrum6767.graph
    sourceMap4914 fusedMap4914 sourceMap4914_checked fusedMap4914_checked
    DegreeTwoThreeFiniteComparisons.comparison4914
#print axioms sourceMap4914_checked
#print axioms fusedMap4914_checked
#print axioms certified4914
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
