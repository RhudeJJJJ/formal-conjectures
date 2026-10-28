/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4887 : Family 10 := level10.get ⟨1338,by decide⟩
def sourceMap4887 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4887 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4887_checked : acceptsGraphIso
    (source (graph core4887) (root 10) 2 2) DegreeTwoThreeSpectrum7416.graph sourceMap4887=true := by decide +kernel
theorem fusedMap4887_checked : acceptsGraphIso
    (fused (graph core4887) (root 10) 2 2) DegreeTwoThreeSpectrum6658.graph fusedMap4887=true := by decide +kernel
theorem certified4887 : Certified (graph core4887) (root 10) 2 2 :=
  of_native_maps core4887 DegreeTwoThreeSpectrum7416.graph DegreeTwoThreeSpectrum6658.graph
    sourceMap4887 fusedMap4887 sourceMap4887_checked fusedMap4887_checked
    DegreeTwoThreeFiniteComparisons.comparison4887
#print axioms sourceMap4887_checked
#print axioms fusedMap4887_checked
#print axioms certified4887
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
