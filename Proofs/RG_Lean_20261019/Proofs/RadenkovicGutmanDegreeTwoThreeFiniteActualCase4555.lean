/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4555 : Family 10 := level10.get ⟨463,by decide⟩
def sourceMap4555 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 2 v)
def fusedMap4555 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4555_checked : acceptsGraphIso
    (source (graph core4555) (root 10) 2 2) DegreeTwoThreeSpectrum6797.graph sourceMap4555=true := by decide +kernel
theorem fusedMap4555_checked : acceptsGraphIso
    (fused (graph core4555) (root 10) 2 2) DegreeTwoThreeSpectrum5906.graph fusedMap4555=true := by decide +kernel
theorem certified4555 : Certified (graph core4555) (root 10) 2 2 :=
  of_native_maps core4555 DegreeTwoThreeSpectrum6797.graph DegreeTwoThreeSpectrum5906.graph
    sourceMap4555 fusedMap4555 sourceMap4555_checked fusedMap4555_checked
    DegreeTwoThreeFiniteComparisons.comparison4555
#print axioms sourceMap4555_checked
#print axioms fusedMap4555_checked
#print axioms certified4555
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
