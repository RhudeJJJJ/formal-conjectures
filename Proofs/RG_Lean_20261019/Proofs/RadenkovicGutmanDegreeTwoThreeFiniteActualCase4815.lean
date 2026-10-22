/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4815 : Family 10 := level10.get ⟨1167,by decide⟩
def sourceMap4815 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4815 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4815_checked : acceptsGraphIso
    (source (graph core4815) (root 10) 2 2) DegreeTwoThreeSpectrum7249.graph sourceMap4815=true := by decide +kernel
theorem fusedMap4815_checked : acceptsGraphIso
    (fused (graph core4815) (root 10) 2 2) DegreeTwoThreeSpectrum6318.graph fusedMap4815=true := by decide +kernel
theorem certified4815 : Certified (graph core4815) (root 10) 2 2 :=
  of_native_maps core4815 DegreeTwoThreeSpectrum7249.graph DegreeTwoThreeSpectrum6318.graph
    sourceMap4815 fusedMap4815 sourceMap4815_checked fusedMap4815_checked
    DegreeTwoThreeFiniteComparisons.comparison4815
#print axioms sourceMap4815_checked
#print axioms fusedMap4815_checked
#print axioms certified4815
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
